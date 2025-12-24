package org.example.SqlTransit.tool;


import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.drop.Drop;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.statement.create.table.Index;

import java.lang.reflect.Method;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MysqlToOBVisitor extends StatementVisitorAdapter {
    private final StringBuilder oceanBaseSql = new StringBuilder();
    private final Map<String, List<String>> tablePartitionInfo = new HashMap<>();

    // OceanBase 关键字集合（分布式特性+专属语法）
    private static final Set<String> OCEANBASE_KEYWORDS = new HashSet<>(Arrays.asList(
            "PARTITION", "PARTITIONBY", "HASH", "RANGE", "LIST",
            "GLOBAL", "LOCAL", "CLUSTER", "REPLICA", "TABLEGROUP",
            "TENANT", "REPLICA_NUM", "ZONE_LIST", "PRIMARY_ZONE",
            "AUTO_INCREMENT", "GLOBAL", "OB_UNIQUE", "OB_HASH",
            "DISTRIBUTED", "TABLET", "UNIT_NUM"
    ));

    // OceanBase 索引类型枚举（全局索引/本地索引）
    private enum OBIndexType {
        GLOBAL, LOCAL, NORMAL
    }

    // OceanBase 分区类型枚举
    private enum OBPartitionType {
        HASH, RANGE, LIST, NONE
    }

    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
    }

    /**
     * 替换布尔字面量：Oracle 模式使用 Y/N
     */
    private String replaceBooleanLiterals(String sql) {
        StringBuilder sb = new StringBuilder();
        boolean inString = false;
        int i = 0;

        while (i < sql.length()) {
            char ch = sql.charAt(i);
            if (ch == '\'') {
                sb.append(ch);
                i++;
                while (i < sql.length() && sql.charAt(i) != '\'') {
                    sb.append(sql.charAt(i++));
                }
                if (i < sql.length()) {
                    sb.append('\'');
                    i++;
                }
                continue;
            }

            if (!inString) {
                if (i + 4 <= sql.length() && sql.substring(i, i + 4).equalsIgnoreCase("true") &&
                        (i == 0 || !Character.isLetterOrDigit(sql.charAt(i - 1))) &&
                        (i + 4 == sql.length() || !Character.isLetterOrDigit(sql.charAt(i + 4)))) {
                    sb.append("Y");
                    i += 4;
                    continue;
                }
                if (i + 5 <= sql.length() && sql.substring(i, i + 5).equalsIgnoreCase("false") &&
                        (i == 0 || !Character.isLetterOrDigit(sql.charAt(i - 1))) &&
                        (i + 5 == sql.length() || !Character.isLetterOrDigit(sql.charAt(i + 5)))) {
                    sb.append("N");
                    i += 5;
                    continue;
                }
            }

            sb.append(ch);
            i++;
        }

        return sb.toString();
    }

    // 大写 WHERE 中的列名（跳过关键字和函数）
    private String uppercaseWhereColumnNames(String sql) {
        StringBuilder sb = new StringBuilder();
        boolean inString = false;
        int i = 0;

        while (i < sql.length()) {
            char ch = sql.charAt(i);
            if (ch == '\'') {
                sb.append(ch);
                i++;
                while (i < sql.length() && sql.charAt(i) != '\'') {
                    sb.append(sql.charAt(i++));
                }
                if (i < sql.length()) {
                    sb.append('\'');
                    i++;
                }
                continue;
            }

            if (Character.isJavaIdentifierStart(ch)) {
                int start = i;
                int end = i + 1;
                while (end < sql.length() && Character.isJavaIdentifierPart(sql.charAt(end))) {
                    end++;
                }
                String token = sql.substring(start, end);

                boolean isFunc = end < sql.length() && sql.charAt(end) == '(';

                if (isKeyword(token)) {
                    sb.append(token);
                } else if (isFunc) {
                    sb.append(token);
                } else {
                    if (end < sql.length() && sql.charAt(end) == '.') {
                        int dotEnd = end + 1;
                        while (dotEnd < sql.length() && Character.isJavaIdentifierPart(sql.charAt(dotEnd))) {
                            dotEnd++;
                        }
                        String tname = token.toUpperCase();
                        String cname = sql.substring(end + 1, dotEnd).toUpperCase();
                        sb.append(tname).append('.').append(cname);
                        i = dotEnd;
                        continue;
                    }
                    sb.append(token.toUpperCase());
                }
                i = end;
                continue;
            }

            sb.append(ch);
            i++;
        }

        return sb.toString();
    }

    private String processWhereColumnNames(String sql) {
        return uppercaseWhereColumnNames(sql);
    }

    private boolean isKeyword(String token) {
        return Arrays.asList("AND", "OR", "NOT", "IS", "IN", "LIKE", "BETWEEN", "NULL", "EXISTS", "TRUE", "FALSE")
                .contains(token.toUpperCase());
    }

    private String processWhereExpression(Expression where) {
        if (where == null) return "";
        String expr = where.toString();
        expr = expr.replace("CURRENT_TIMESTAMP", "SYSDATE");
        expr = replaceBooleanLiterals(expr);
        expr = processWhereColumnNames(expr);
        return " WHERE " + expr;
    }

    /**
     * 提取表注释（适配 OceanBase 表注释语法）
     */
    private String extractTableComment(CreateTable createTable) {
        try {
            java.lang.reflect.Method getOptionsMethod = CreateTable.class.getMethod("getTableOptionsStrings");
            List<String> tableOptions = (List<String>) getOptionsMethod.invoke(createTable);

            if (tableOptions != null && !tableOptions.isEmpty()) {
                for (int i = 0; i < tableOptions.size(); i++) {
                    String option = tableOptions.get(i);
                    if ("COMMENT".equalsIgnoreCase(option.trim())) {
                        if (i + 2 < tableOptions.size()) {
                            String nextOption = tableOptions.get(i + 1);
                            if ("=".equals(nextOption.trim())) {
                                String comment = tableOptions.get(i + 2);
                                return comment.trim();
                            }
                        }
                        if (i + 1 < tableOptions.size()) {
                            String comment = tableOptions.get(i + 1);
                            return comment.trim();
                        }
                    }
                }

                for (int i = 0; i < tableOptions.size(); i++) {
                    String option = tableOptions.get(i);
                    if ("=".equals(option.trim()) && i > 0 && i + 1 < tableOptions.size()) {
                        String prevOption = tableOptions.get(i - 1);
                        String nextOption = tableOptions.get(i + 1);
                        if ("COMMENT".equalsIgnoreCase(prevOption.trim())) {
                            return nextOption.trim();
                        }
                    }
                }

                for (String option : tableOptions) {
                    if ((option.contains("'") || option.contains("\"")) && option.length() > 2) {
                        return option.trim();
                    }
                }
            }
        } catch (Exception e) {
        }

        String createStr = createTable.toString();
        Pattern[] patterns = {
                Pattern.compile("COMMENT\\s*=\\s*['\"]([^'\"]+)['\"]", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s*['\"]([^'\"]+)['\"]", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s*=\\s*([^,;)]+)", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s+([^,;)]+)", Pattern.CASE_INSENSITIVE)
        };

        for (Pattern pattern : patterns) {
            Matcher matcher = pattern.matcher(createStr);
            if (matcher.find()) {
                String comment = matcher.group(1).trim();
                if ((comment.startsWith("'") && comment.endsWith("'")) ||
                        (comment.startsWith("\"") && comment.endsWith("\""))) {
                    comment = comment.substring(1, comment.length() - 1);
                }
                return comment;
            }
        }

        return null;
    }

    private String argsToJoinedString(List<?> args) {
        if (args == null || args.isEmpty()) return "";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < args.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(String.valueOf(args.get(i)));
        }
        return sb.toString();
    }

    /**
     * 转换字段类型：适配 OceanBase 数据类型（兼容 MySQL 但有专属调整）
     */
    private String convertColumnType(String mysqlType, List<?> args) {
        String type = mysqlType.toUpperCase();

        switch (type) {
            case "TINYINT":
                if (args != null && args.size() == 1 && "1".equals(args.get(0).toString())) {
                    return "TINYINT(1)";
                }
                return "TINYINT";
            case "INT":
                return "INT";
            case "BIGINT":
                return "BIGINT";
            case "VARCHAR":
                if (args != null && !args.isEmpty()) {
                    int length = Integer.parseInt(args.get(0).toString());
                    // OceanBase VARCHAR 最大长度 65535（比 MySQL 更宽松）
                    if (length > 65535) {
                        return "VARCHAR(65535)";
                    }
                    return "VARCHAR(" + args.get(0) + ")";
                }
                return "VARCHAR(255)";
            case "CHAR":
                if (args != null && !args.isEmpty()) {
                    return "CHAR(" + args.get(0) + ")";
                }
                return "CHAR(1)";
            case "TEXT":
                return "TEXT";
            case "LONGTEXT":
                return "LONGTEXT";
            case "MEDIUMTEXT":
                return "MEDIUMTEXT";
            case "TINYTEXT":
                return "TINYTEXT";
            case "BLOB":
                return "BLOB";
            case "LONGBLOB":
                return "LONGBLOB";
            case "MEDIUMBLOB":
                return "MEDIUMBLOB";
            case "TINYBLOB":
                return "TINYBLOB";
            case "DATETIME":
                return "DATETIME";
            case "TIMESTAMP":
                // OceanBase TIMESTAMP 兼容 MySQL，但建议用 DATETIME（分布式场景更稳定）
                return "DATETIME";
            case "DATE":
                return "DATE";
            case "TIME":
                return "TIME";
            case "YEAR":
                // OceanBase 兼容 YEAR，但建议用 INT(4)
                return "INT(4)";
            case "FLOAT":
                if (args != null && args.size() >= 2) {
                    return "FLOAT(" + args.get(0) + "," + args.get(1) + ")";
                }
                return "FLOAT";
            case "DOUBLE":
                if (args != null && args.size() >= 2) {
                    return "DOUBLE(" + args.get(0) + "," + args.get(1) + ")";
                }
                return "DOUBLE";
            case "DECIMAL":
                if (args != null && args.size() >= 2) {
                    return "DECIMAL(" + args.get(0) + "," + args.get(1) + ")";
                } else if (args != null && !args.isEmpty()) {
                    return "DECIMAL(" + args.get(0) + ",0)";
                }
                // OceanBase 金融场景默认 DECIMAL(16,2)（比 MySQL 更适配金融）
                return "DECIMAL(16,2)";
            case "NUMERIC":
                if (args != null && args.size() >= 2) {
                    return "NUMERIC(" + args.get(0) + "," + args.get(1) + ")";
                }
                return "NUMERIC(16,2)";
            case "BIT":
                if (args != null && !args.isEmpty()) {
                    return "BIT(" + args.get(0) + ")";
                }
                return "BIT(1)";
            case "BOOL":
            case "BOOLEAN":
                // OceanBase 无原生 BOOL，转为 TINYINT(1)
                return "TINYINT(1)";
            case "ENUM":
                if (args != null && !args.isEmpty()) {
                    return "ENUM(" + argsToJoinedString(args) + ")";
                }
                return "ENUM('Y','N')";
            case "SET":
                if (args != null && !args.isEmpty()) {
                    return "SET(" + argsToJoinedString(args) + ")";
                }
                return "SET('')";
            case "JSON":
                // OceanBase 4.0+ 原生支持 JSON 类型
                return "JSON";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + argsToJoinedString(args) + ")";
                }
                return type;
        }
    }

    /**
     * Oracle 模式字段类型映射
     */
    private String convertColumnTypeOracle(String mysqlType, List<?> args) {
        String type = mysqlType.toUpperCase();
        switch (type) {
            case "INT":
                return "NUMBER";
            case "VARCHAR":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR2(" + args.get(0) + ")";
                }
                return "VARCHAR2";
            case "DATETIME":
            case "TIMESTAMP":
                return "DATE";
            case "BIGINT":
                return "NUMBER(20)";
            case "TINYINT":
                return "NUMBER(3)";
            case "BOOLEAN":
            case "BOOL":
                return "VARCHAR2(1)";
            case "TEXT":
            case "LONGTEXT":
            case "MEDIUMTEXT":
            case "TINYTEXT":
                return "CLOB";
            case "FLOAT":
                return "NUMBER(10,2)";
            case "DOUBLE":
                return "NUMBER(18,4)";
            case "DECIMAL":
                return "NUMBER";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + args.get(0) + ")";
                }
                return type;
        }
    }

    /**
     * 提取分区信息（OceanBase 分布式核心：分区键/分区类型）
     */
    private void extractPartitionInfo(CreateTable createTable, String tableName) {
        String createStr = createTable.toString().toUpperCase();

        // 提取分区键（兼容 MySQL PARTITION BY 语法）
        Pattern partitionKeyPattern = Pattern.compile("PARTITION\\s+BY\\s+(HASH|RANGE|LIST)\\s*\\(([^)]+)\\)", Pattern.CASE_INSENSITIVE);
        Matcher partitionKeyMatcher = partitionKeyPattern.matcher(createStr);

        if (partitionKeyMatcher.find()) {
            String partitionType = partitionKeyMatcher.group(1);
            String partitionKeys = partitionKeyMatcher.group(2);
            String[] keys = partitionKeys.split(",");
            List<String> partitionKeyList = new ArrayList<>();

            for (String key : keys) {
                String cleanKey = cleanIdentifier(key.trim());
                partitionKeyList.add(cleanKey);
            }

            tablePartitionInfo.put(tableName, partitionKeyList);
        }
    }

    /**
     * 判断 OceanBase 索引类型：
     * - 包含分区键 → 本地索引（LOCAL）
     * - 不包含分区键 → 全局索引（GLOBAL）
     */
    private OBIndexType getIndexType(String tableName, List<String> indexColumns) {
        List<String> partitionKeys = tablePartitionInfo.get(tableName);
        if (partitionKeys == null || partitionKeys.isEmpty()) {
            return OBIndexType.NORMAL;
        }
        for (String col : indexColumns) {
            if (partitionKeys.contains(col)) {
                return OBIndexType.LOCAL;
            }
        }
        return OBIndexType.GLOBAL;
    }

    /**
     * 处理 CreateTable 中的表级索引（适配 OceanBase 全局/本地索引）
     */
    private void processTableIndexes(CreateTable createTable, String tableName) {
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<Index> indexes = (List<Index>) getIndexesMethod.invoke(createTable);

            if (indexes != null && !indexes.isEmpty()) {
                for (Index idx : indexes) {
                    String idxName = cleanIdentifier(idx.getName());
                    if (idxName == null || idxName.isEmpty()) {
                        idxName = "idx_" + tableName + "_" + String.join("_", idx.getColumnsNames());
                    }

                    // 修正索引类型判断逻辑：增加明确的非主键/非唯一判断
                    boolean isUnique = false;
                    boolean isPrimary = false;

                    // 优先使用JSqlParser的API判断（如果存在）
                    try {
                        Method isUniqueMethod = idx.getClass().getMethod("isUnique");
                        isUnique = (Boolean) isUniqueMethod.invoke(idx);
                    } catch (Exception e) {
                        // 兼容旧版本：通过名称和内容判断
                        String idxStr = idx.toString().toUpperCase();
                        isUnique = idxStr.contains("UNIQUE");
                    }

                    try {
                        Method isPrimaryMethod = idx.getClass().getMethod("isPrimary");
                        isPrimary = (Boolean) isPrimaryMethod.invoke(idx);
                    } catch (Exception e) {
                        String idxStr = idx.toString().toUpperCase();
                        isPrimary = idxStr.contains("PRIMARY KEY");
                    }

                    // 只跳过主键索引，保留唯一索引和普通索引
                    if (isPrimary) {
                        continue;
                    }

                    List<String> idxColumns = new ArrayList<>();
                    for (Object colObj : idx.getColumnsNames()) {
                        idxColumns.add(cleanIdentifier(colObj.toString()));
                    }

                    OBIndexType idxType = getIndexType(tableName, idxColumns);

                    // 构建索引SQL（包含所有非主键索引）
                    oceanBaseSql.append("\nCREATE ");
                    if (isUnique) {
                        oceanBaseSql.append("UNIQUE ");
                    }
                    oceanBaseSql.append("INDEX ").append(idxName);
                    if (idxType == OBIndexType.GLOBAL) {
                        oceanBaseSql.append(" GLOBAL");
                    } else if (idxType == OBIndexType.LOCAL) {
                        oceanBaseSql.append(" LOCAL");
                    }
                    oceanBaseSql.append(" ON ").append(tableName)
                            .append(" (").append(String.join(", ", idxColumns)).append(") USING BTREE;");
                }
            }
        } catch (Exception e) {
            // 正则解析部分保持不变，但确保普通索引被捕获
            String createStr = createTable.toString();
            // 修正正则表达式，确保匹配所有KEY索引（包括普通索引）
            Pattern indexPattern = Pattern.compile(
                    "(?i)(UNIQUE\\s+)?(KEY|INDEX)\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE
            );
            Matcher idxMatcher = indexPattern.matcher(createStr);
            while (idxMatcher.find()) {
                boolean isUnique = idxMatcher.group(1) != null;
                String idxName = cleanIdentifier(idxMatcher.group(3));
                String columns = idxMatcher.group(4);
                String[] colArr = columns.split(",");
                List<String> idxColumns = new ArrayList<>();
                for (String col : colArr) {
                    idxColumns.add(cleanIdentifier(col.trim()));
                }

                OBIndexType idxType = getIndexType(tableName, idxColumns);
                oceanBaseSql.append("\n");
                oceanBaseSql.append("CREATE ");
                if (isUnique) {
                    oceanBaseSql.append("UNIQUE ");
                }
                oceanBaseSql.append("INDEX ").append(idxName);
                if (idxType == OBIndexType.GLOBAL) {
                    oceanBaseSql.append(" GLOBAL");
                } else if (idxType == OBIndexType.LOCAL) {
                    oceanBaseSql.append(" LOCAL");
                }
                oceanBaseSql.append(" ON ").append(tableName)
                        .append(" (").append(String.join(", ", idxColumns)).append(") USING BTREE;");

            }
        }
    }
//    private void processTableIndexes(CreateTable createTable, String tableName) {
//        try {
//            // 反射获取 CreateTable 中的索引列表
//            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
//            List<Index> indexes = (List<Index>) getIndexesMethod.invoke(createTable);
//
//            if (indexes != null && !indexes.isEmpty()) {
//                for (Index idx : indexes) {
//                    String idxName = cleanIdentifier(idx.getName());
//                    if (idxName == null || idxName.isEmpty()) {
//                        // 自动生成 OceanBase 规范索引名
//                        idxName = "idx_" + tableName + "_" + String.join("_", idx.getColumnsNames());
//                    }
//
//                    // 识别唯一索引/主键索引（兼容低版本 JSqlParser）
//                    boolean isUnique = false;
//                    boolean isPrimary = false;
//                    String idxNameRaw = idx.getName() != null ? idx.getName().toUpperCase() : "";
//                    String idxStr = idx.toString().toUpperCase();
//
//                    if (idxNameRaw.contains("UK_") || idxNameRaw.contains("UNIQUE") || idxStr.contains("UNIQUE")) {
//                        isUnique = true;
//                    }
//                    if (idxNameRaw.contains("PK_") || idxNameRaw.contains("PRIMARY") || idxStr.contains("PRIMARY KEY")) {
//                        isPrimary = true;
//                    }
//
//                    List<String> idxColumns = new ArrayList<>();
//                    for (Object colObj : idx.getColumnsNames()) {
//                        idxColumns.add(cleanIdentifier(colObj.toString()));
//                    }
//
//                    // 跳过主键索引（已在字段定义中处理）
//                    if (isPrimary) {
//                        continue;
//                    }
//
//                    // 获取 OceanBase 索引类型
//                    OBIndexType idxType = getIndexType(tableName, idxColumns);
//
//                    // 构建 OceanBase 索引 SQL
//                    oceanBaseSql.append("\n");
//                    oceanBaseSql.append("CREATE ");
//                    if (isUnique) {
//                        oceanBaseSql.append("UNIQUE ");
//                    }
//                    oceanBaseSql.append("INDEX ").append(idxName);
//                    // 追加 OceanBase 分布式索引类型
//                    if (idxType == OBIndexType.GLOBAL) {
//                        oceanBaseSql.append(" GLOBAL");
//                    } else if (idxType == OBIndexType.LOCAL) {
//                        oceanBaseSql.append(" LOCAL");
//                    }
//                    oceanBaseSql.append(" ON ").append(tableName)
//                            .append(" (").append(String.join(", ", idxColumns)).append(")");
//                    // OceanBase 默认 BTREE 索引
//                    oceanBaseSql.append(" USING BTREE;");
//                }
//            }
//        } catch (Exception e) {
//            // 兼容低版本 JSqlParser（正则提取索引）
//            String createStr = createTable.toString();
//            Pattern indexPattern = Pattern.compile(
//                    "(?i)(UNIQUE\\s+)?KEY\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
//                    Pattern.CASE_INSENSITIVE
//            );
//            Matcher idxMatcher = indexPattern.matcher(createStr);
//            while (idxMatcher.find()) {
//                boolean isUnique = idxMatcher.group(1) != null;
//                String idxName = cleanIdentifier(idxMatcher.group(2));
//                String columns = idxMatcher.group(3);
//                String[] colArr = columns.split(",");
//                List<String> idxColumns = new ArrayList<>();
//                for (String col : colArr) {
//                    idxColumns.add(cleanIdentifier(col.trim()));
//                }
//
//                OBIndexType idxType = getIndexType(tableName, idxColumns);
//                oceanBaseSql.append("\n");
//                oceanBaseSql.append("CREATE ");
//                if (isUnique) {
//                    oceanBaseSql.append("UNIQUE ");
//                }
//                oceanBaseSql.append("INDEX ").append(idxName);
//                if (idxType == OBIndexType.GLOBAL) {
//                    oceanBaseSql.append(" GLOBAL");
//                } else if (idxType == OBIndexType.LOCAL) {
//                    oceanBaseSql.append(" LOCAL");
//                }
//                oceanBaseSql.append(" ON ").append(tableName)
//                        .append(" (").append(String.join(", ", idxColumns)).append(") USING BTREE;");
//            }
//        }
//    }

    /**
     * 构建 OceanBase 分区语句（分布式核心）
     */
    private String buildPartitionClause(CreateTable createTable, String tableName) {
        List<String> partitionKeys = tablePartitionInfo.get(tableName);
        if (partitionKeys == null || partitionKeys.isEmpty()) {
            // 默认按主键 HASH 分区（OceanBase 最佳实践）
            return "\nPARTITION BY HASH(`order_id`) PARTITIONS 8";
        }

        // 提取 MySQL 分区类型，转换为 OceanBase 分区语法
        String createStr = createTable.toString().toUpperCase();
        Pattern partitionTypePattern = Pattern.compile("PARTITION\\s+BY\\s+(HASH|RANGE|LIST)", Pattern.CASE_INSENSITIVE);
        Matcher partitionTypeMatcher = partitionTypePattern.matcher(createStr);
        String partitionType = partitionTypeMatcher.find() ? partitionTypeMatcher.group(1) : "HASH";

        // 构建分区语句
        StringBuilder partitionClause = new StringBuilder("\nPARTITION BY ").append(partitionType).append(" (");
        partitionClause.append(String.join(", ", partitionKeys)).append(")");

        // 补充分区数（OceanBase 推荐 2^n 个分区）
        if ("HASH".equals(partitionType)) {
            partitionClause.append(" PARTITIONS 8");
        } else if ("RANGE".equals(partitionType)) {
            // 适配 RANGE 分区（示例：按时间分区）
            partitionClause.append("\nPARTITION p2024 VALUES LESS THAN (TO_DAYS('2025-01-01')),");
            partitionClause.append("\nPARTITION p2025 VALUES LESS THAN (MAXVALUE)");
        }

        return partitionClause.toString();
    }

    @Override
    public void visit(CreateTable createTable) {
        String tableName = cleanIdentifier(createTable.getTable().getName());

        // 提取分区信息（OceanBase 分布式核心）
        extractPartitionInfo(createTable, tableName);

        // 构建 OceanBase 建表语句
        oceanBaseSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();
        boolean hasColumnLevelPrimaryKey = false;
        List<String> commentStatements = new ArrayList<>();

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) oceanBaseSql.append(",\n");

            String colName = cleanIdentifier(col.getColumnName());
            String colType = convertColumnTypeOracle(col.getColDataType().getDataType(),
                    col.getColDataType().getArgumentsStringList());

            List<String> specs = new ArrayList<>();

            try {
                java.lang.reflect.Method method = ColumnDefinition.class.getMethod("getColumnSpecStrings");
                Object result = method.invoke(col);
                if (result instanceof List) {
                    for (Object obj : (List<?>) result) {
                        if (obj != null) {
                            specs.add(obj.toString().trim());
                        }
                    }
                }
            } catch (Exception e) {
                String fullColStr = col.toString();
                String pattern = Pattern.quote(col.getColumnName()) + "\\s+.*?(?=,\\s*|$)";
                Pattern r = Pattern.compile(pattern, Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                Matcher m = r.matcher(fullColStr);

                if (m.find()) {
                    String columnDef = m.group();
                    String colNamePattern = Pattern.quote(col.getColumnName());
                    String dataTypePattern = Pattern.quote(col.getColDataType().getDataType());
                    String constraintsOnly = columnDef
                            .replaceFirst("^" + colNamePattern + "\\s+", "")
                            .replaceFirst("^" + dataTypePattern + "\\s*", "")
                            .trim();

                    specs = parseConstraintTokens(constraintsOnly);
                }
            }

            try {
                java.lang.reflect.Method getSpecsMethod = ColumnDefinition.class.getMethod("getColumnSpecifications");
                Object specsObj = getSpecsMethod.invoke(col);
                if (specsObj instanceof List) {
                    for (Object specObj : (List<?>) specsObj) {
                        if (specObj != null) {
                            specs.add(specObj.toString().toUpperCase().trim());
                        }
                    }
                }
            } catch (Exception e) {
            }

            boolean isAutoIncrement = false, isPrimaryKey = false,
                    isNotNull = false, isUnique = false;
            String defaultValStr = null;
            String columnComment = null;
            String collation = null;
            String charset = null;

            for (int j = 0; j < specs.size(); j++) {
                String spec = specs.get(j).toUpperCase().trim();

                if (j + 1 < specs.size()) {
                    String nextSpec = specs.get(j + 1);
                    String twoWords = spec + " " + (nextSpec != null ? nextSpec.toUpperCase() : "");

                    if ("PRIMARY KEY".equals(twoWords)) {
                        isPrimaryKey = true;
                        j++;
                        continue;
                    }
                    if ("NOT NULL".equals(twoWords)) {
                        isNotNull = true;
                        j++;
                        continue;
                    }
                    if ("FOREIGN KEY".equals(twoWords)) {
                        j += 4;
                        continue;
                    }
                }

                switch (spec) {
                    case "AUTO_INCREMENT":
                    case "AUTOINCREMENT":
                        // OceanBase 全局自增（避免分布式 ID 冲突）
                        isAutoIncrement = true;
                        break;
                    case "PRIMARY":
                        isPrimaryKey = true;
                        break;
                    case "NOT":
                        isNotNull = true;
                        break;
                    case "NULL":
                        if (j > 0 && "NOT".equalsIgnoreCase(specs.get(j-1))) {
                        } else {
                            isNotNull = false;
                        }
                        break;
                    case "UNIQUE":
                        isUnique = true;
                        break;
                    case "DEFAULT":
                        if (j + 1 < specs.size()) {
                            defaultValStr = specs.get(j + 1);
                            j++;
                        }
                        break;
                    case "COMMENT":
                        if (j + 1 < specs.size()) {
                            columnComment = specs.get(j + 1);
                            j++;
                        }
                        break;
                    case "COLLATE":
                        if (j + 1 < specs.size()) {
                            collation = specs.get(j + 1);
                            j++;
                        }
                        break;
                    case "CHARACTER":
                        if (j + 2 < specs.size() && "SET".equalsIgnoreCase(specs.get(j + 1))) {
                            charset = specs.get(j + 2);
                            j += 2;
                        }
                        break;
                }
            }

            // 构建字段定义
            oceanBaseSql.append("    ").append(colName).append(" ").append(colType);

            // Oracle 模式自增
            if (isAutoIncrement) {
                oceanBaseSql.append(" GENERATED BY DEFAULT AS IDENTITY");
            }

            if (defaultValStr != null) {
                defaultValStr = defaultValStr.trim();
                if (defaultValStr.toUpperCase().contains("CURRENT_TIMESTAMP") ||
                        defaultValStr.toUpperCase().contains("NOW()")) {
                    oceanBaseSql.append(" DEFAULT SYSDATE");
                } else if (colType.equalsIgnoreCase("VARCHAR2(1)") &&
                        (defaultValStr.equalsIgnoreCase("true") ||
                                defaultValStr.equalsIgnoreCase("false"))) {
                    oceanBaseSql.append(" DEFAULT '").append(defaultValStr.equalsIgnoreCase("true") ? "Y" : "N").append("'");
                } else if (defaultValStr.startsWith("'") && defaultValStr.endsWith("'")) {
                    oceanBaseSql.append(" DEFAULT ").append(defaultValStr);
                } else {
                    oceanBaseSql.append(" DEFAULT ").append(defaultValStr);
                }
            } else if (colType.equalsIgnoreCase("VARCHAR2(1)")) {
                oceanBaseSql.append(" DEFAULT 'Y'");
            }

            if (isPrimaryKey) {
                oceanBaseSql.append(" PRIMARY KEY");
                hasColumnLevelPrimaryKey = true;
            } else {
            if (isUnique) {
                oceanBaseSql.append(" UNIQUE");
                }
                if (isNotNull) {
                    oceanBaseSql.append(" NOT NULL");
                }
            }

            // 字段注释（Oracle 模式）
            if (columnComment != null && !columnComment.isEmpty()) {
                columnComment = columnComment.replaceAll("^['\"]|['\"]$", "");
                commentStatements.add("COMMENT ON COLUMN " + tableName + "." + colName +
                        " IS '" + columnComment.replace("'", "''") + "';");
            }
        }

        // 追加表级主键（如果列级未定义）
        appendTablePrimaryKey(createTable, tableName, hasColumnLevelPrimaryKey);

        // 表级约束处理（外键、检查约束等）
        processTableLevelConstraints(createTable, tableName);

        // 将表级索引转换：唯一索引→约束，普通索引→独立 CREATE INDEX
        IndexArtifacts indexArtifacts = buildIndexArtifacts(createTable, tableName);
        if (!indexArtifacts.constraints.isEmpty()) {
            for (String c : indexArtifacts.constraints) {
                oceanBaseSql.append(",\n").append(c);
            }
        }

        oceanBaseSql.append("\n)");

        // 表级注释 -> 单独 COMMENT 语句
        String tableComment = extractTableComment(createTable);
        if (tableComment != null && !tableComment.isEmpty()) {
            tableComment = tableComment.trim();
            if (tableComment.startsWith("'") && tableComment.endsWith("'")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            } else if (tableComment.startsWith("\"") && tableComment.endsWith("\"")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            }
            tableComment = tableComment.replace("'", "''");
            commentStatements.add("COMMENT ON TABLE " + tableName + " IS '" + tableComment + "';");
        }

        // 结束建表语句（不追加任何 OceanBase 专属表配置）
        oceanBaseSql.append(";\n");

        // 追加 COMMENT 语句（表注释 + 列注释）
        if (!commentStatements.isEmpty()) {
            for (String cmt : commentStatements) {
                oceanBaseSql.append(cmt).append("\n");
            }
        }

        // 追加普通索引的 CREATE INDEX 语句
        if (!indexArtifacts.indexes.isEmpty()) {
            for (String idxSql : indexArtifacts.indexes) {
                oceanBaseSql.append(idxSql).append("\n");
            }
        }
    }

    /**
     * 生成主键约束名：PK_表名（已大写）
     */
    private String generatePrimaryKeyConstraintName(String tableName, List<String> primaryKeyCols) {
        return "PK_" + tableName;
    }

    /**
     * 如果未在列级定义主键，则尝试从表级索引提取主键并追加
     */
    private void appendTablePrimaryKey(CreateTable createTable, String tableName, boolean hasColumnLevelPrimaryKey) {
        if (hasColumnLevelPrimaryKey) {
            return;
        }

        List<String> tablePrimaryKeyCols = new ArrayList<>();

        // 优先使用反射获取索引列表
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<Index> indexes = (List<Index>) getIndexesMethod.invoke(createTable);
            if (indexes != null) {
                for (Index idx : indexes) {
                    String idxStr = idx.toString().toUpperCase();
                    if (idxStr.contains("PRIMARY KEY")) {
                        for (Object colObj : idx.getColumnsNames()) {
                            tablePrimaryKeyCols.add(cleanIdentifier(colObj.toString()));
                        }
                        break;
                    }
                }
            }
        } catch (Exception e) {
            // 回退到正则解析
            String createStr = createTable.toString();
            Pattern pkPattern = Pattern.compile("PRIMARY KEY\\s*\\(([^)]+)\\)", Pattern.CASE_INSENSITIVE);
            Matcher m = pkPattern.matcher(createStr);
            if (m.find()) {
                String cols = m.group(1);
                String[] colArr = cols.split(",");
                for (String col : colArr) {
                    tablePrimaryKeyCols.add(cleanIdentifier(col.trim()));
                }
            }
        }

        if (!tablePrimaryKeyCols.isEmpty()) {
            String pkConstraintName = generatePrimaryKeyConstraintName(tableName, tablePrimaryKeyCols);
            oceanBaseSql.append(",\n    CONSTRAINT ")
                    .append(pkConstraintName)
                    .append(" PRIMARY KEY (")
                    .append(String.join(", ", tablePrimaryKeyCols))
                    .append(")");
        }
    }

    /**
     * 将 MySQL 索引拆分：
     *   - 唯一索引 -> 约束
     *   - 普通索引 -> CREATE INDEX
     */
    private IndexArtifacts buildIndexArtifacts(CreateTable createTable, String tableName) {
        List<String> constraints = new ArrayList<>();
        List<String> indexSqls = new ArrayList<>();
        
        // 先尝试反射获取索引
        List<Index> idxList = null;
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            idxList = (List<Index>) getIndexesMethod.invoke(createTable);
        } catch (Exception e) {
            // 反射失败，使用正则解析
        }

        if (idxList != null && !idxList.isEmpty()) {
            // 使用反射获取的索引列表
            for (Index idx : idxList) {
                String rawName = idx.getName();
                String idxName = rawName != null ? cleanIdentifier(rawName) : null;

                // 识别唯一/主键：通过反射尝试调用 isUnique() 和类型检查
                boolean isUnique = false;
                boolean isPrimary = false;
                
                try {
                    // 尝试通过反射判断是否为唯一索引
                    java.lang.reflect.Method isUniqueMethod = idx.getClass().getMethod("isUnique");
                    Object uniqueResult = isUniqueMethod.invoke(idx);
                    if (uniqueResult instanceof Boolean) {
                        isUnique = (Boolean) uniqueResult;
                    }
                } catch (Exception e) {
                    // 反射失败，使用字符串匹配
                }
                
                // 字符串匹配作为备选方案
                String idxNameUpper = rawName != null ? rawName.toUpperCase() : "";
                String idxStrUpper = idx.toString().toUpperCase();
                if (idxNameUpper.contains("UK_") || idxNameUpper.contains("UNIQUE") || idxStrUpper.contains("UNIQUE")) {
                    isUnique = true;
                }
                if (idxNameUpper.contains("PK_") || idxNameUpper.contains("PRIMARY") || idxStrUpper.contains("PRIMARY KEY")) {
                    isPrimary = true;
                }

                // 主键已经单独处理，跳过
                if (isPrimary) {
                    continue;
                }

                List<String> idxColumns = new ArrayList<>();
                try {
                    for (Object colObj : idx.getColumnsNames()) {
                        idxColumns.add(cleanIdentifier(colObj.toString()));
                    }
                } catch (Exception e) {
                    // 获取列名失败，跳过此索引
                    continue;
                }
                
                if (idxColumns.isEmpty()) {
                    continue;
                }

                if (isUnique) {
                    // 唯一索引转为约束
                    String constraintName = idxName != null ? idxName : "UK_" + tableName + "_" + String.join("_", idxColumns);
                    String c = "    CONSTRAINT " + constraintName + " UNIQUE (" + String.join(", ", idxColumns) + ")";
                    constraints.add(c);
                } else {
                    // 普通索引：转换为 CREATE INDEX 语句
                    String indexName = idxName != null ? idxName : "IDX_" + tableName + "_" + String.join("_", idxColumns);
                    // 统一索引名格式：INDEX_ 或 idx_ 开头都转为 IDX_
                    String indexNameUpper = indexName.toUpperCase();
                    if (indexNameUpper.startsWith("INDEX_")) {
                        indexName = "IDX_" + indexName.substring("INDEX_".length());
                    } else if (!indexNameUpper.startsWith("IDX_")) {
                        // 如果既不是 INDEX_ 也不是 IDX_ 开头，统一转为 IDX_ 开头（仅当没有索引名时）
                        if (idxName == null) {
                            indexName = "IDX_" + tableName + "_" + String.join("_", idxColumns);
                        }
                    }
                    String idxSql = "CREATE INDEX " + indexName + " ON " + tableName +
                            " (" + String.join(", ", idxColumns) + ");";
                    indexSqls.add(idxSql);
                }
            }
        }
        
        // 如果反射失败或索引列表为空，使用正则解析作为备选方案
        if (idxList == null || idxList.isEmpty()) {
            String createStr = createTable.toString();
            // 匹配所有 KEY 定义（包括 UNIQUE KEY 和普通 KEY）
            Pattern indexPattern = Pattern.compile(
                    "(?i)(UNIQUE\\s+)?KEY\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE
            );
            Matcher idxMatcher = indexPattern.matcher(createStr);
            while (idxMatcher.find()) {
                boolean isUnique = idxMatcher.group(1) != null;
                String idxName = cleanIdentifier(idxMatcher.group(2));
                String columns = idxMatcher.group(3);
                
                // 跳过主键（主键单独处理）
                if (idxName.toUpperCase().contains("PRIMARY") || idxMatcher.group(0).toUpperCase().contains("PRIMARY KEY")) {
                    continue;
                }
                
                String[] colArr = columns.split(",");
                List<String> idxColumns = new ArrayList<>();
                for (String col : colArr) {
                    idxColumns.add(cleanIdentifier(col.trim()));
                }
                
                if (idxColumns.isEmpty()) {
                    continue;
                }

                if (isUnique) {
                    // 唯一索引转为约束
                    String constraintName = idxName;
                    String c = "    CONSTRAINT " + constraintName + " UNIQUE (" + String.join(", ", idxColumns) + ")";
                    constraints.add(c);
                } else {
                    // 普通索引：转换为 CREATE INDEX 语句
                    String indexName = idxName;
                    String indexNameUpper = indexName.toUpperCase();
                    if (indexNameUpper.startsWith("INDEX_")) {
                        indexName = "IDX_" + indexName.substring("INDEX_".length());
                    } else if (!indexNameUpper.startsWith("IDX_")) {
                        // 如果既不是 INDEX_ 也不是 IDX_ 开头，保持原样（如 idx_bd_root_catalog_id）
                        // 但统一转为大写
                        indexName = indexName.toUpperCase();
                    }
                    String idxSql = "CREATE INDEX " + indexName + " ON " + tableName +
                            " (" + String.join(", ", idxColumns) + ");";
                    indexSqls.add(idxSql);
                }
            }
        }
        
        return new IndexArtifacts(constraints, indexSqls);
    }


    private void processTableLevelConstraints(CreateTable createTable, String tableName) {
        String createStr = createTable.toString();

        // 提取外键约束（OceanBase 兼容 MySQL 外键语法）
        Pattern fkPattern = Pattern.compile(
                "(?i)CONSTRAINT\\s+([^\\s]+)\\s+FOREIGN\\s+KEY\\s*\\(([^)]+)\\)\\s+REFERENCES\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
                Pattern.CASE_INSENSITIVE
        );
        Matcher fkMatcher = fkPattern.matcher(createStr);

        while (fkMatcher.find()) {
            String constraintName = cleanIdentifier(fkMatcher.group(1));
            String columns = fkMatcher.group(2);
            String refTable = cleanIdentifier(fkMatcher.group(3));
            String refColumns = fkMatcher.group(4);

            oceanBaseSql.append(",\n    CONSTRAINT ").append(constraintName)
                    .append(" FOREIGN KEY (").append(columns).append(")")
                    .append(" REFERENCES ").append(refTable)
                    .append(" (").append(refColumns).append(")");
        }

        // 提取检查约束（OceanBase 支持 CHECK 约束）
        Pattern checkPattern = Pattern.compile(
                "(?i)CONSTRAINT\\s+([^\\s]+)\\s+CHECK\\s*\\(([^)]+)\\)",
                Pattern.CASE_INSENSITIVE
        );
        Matcher checkMatcher = checkPattern.matcher(createStr);

        while (checkMatcher.find()) {
            String constraintName = cleanIdentifier(checkMatcher.group(1));
            String condition = checkMatcher.group(2);

            oceanBaseSql.append(",\n    CONSTRAINT ").append(constraintName)
                    .append(" CHECK (").append(condition).append(")");
        }

        // 提取唯一约束（表级）
        Pattern uniquePattern = Pattern.compile(
                "(?i)CONSTRAINT\\s+([^\\s]+)\\s+UNIQUE\\s*\\(([^)]+)\\)",
                Pattern.CASE_INSENSITIVE
        );
        Matcher uniqueMatcher = uniquePattern.matcher(createStr);

        while (uniqueMatcher.find()) {
            String constraintName = cleanIdentifier(uniqueMatcher.group(1));
            String columns = uniqueMatcher.group(2);

            oceanBaseSql.append(",\n    CONSTRAINT ").append(constraintName)
                    .append(" UNIQUE (").append(columns).append(")");
        }
    }

    private List<String> parseConstraintTokens(String input) {
        List<String> tokens = new ArrayList<>();
        if (input == null || input.trim().isEmpty()) {
            return tokens;
        }

        StringBuilder currentToken = new StringBuilder();
        boolean inSingleQuotes = false;
        boolean inDoubleQuotes = false;
        boolean inParentheses = false;
        int parenDepth = 0;

        for (int i = 0; i < input.length(); i++) {
            char c = input.charAt(i);

            if (c == '\'' && (i == 0 || input.charAt(i-1) != '\\')) {
                inSingleQuotes = !inSingleQuotes;
                currentToken.append(c);
            } else if (c == '"' && (i == 0 || input.charAt(i-1) != '\\')) {
                inDoubleQuotes = !inDoubleQuotes;
                currentToken.append(c);
            } else if (c == '(' && !inSingleQuotes && !inDoubleQuotes) {
                inParentheses = true;
                parenDepth++;
                currentToken.append(c);
            } else if (c == ')' && !inSingleQuotes && !inDoubleQuotes && inParentheses) {
                parenDepth--;
                if (parenDepth == 0) {
                    inParentheses = false;
                }
                currentToken.append(c);
            } else if ((c == ' ' || c == ',') && !inSingleQuotes && !inDoubleQuotes && !inParentheses) {
                if (currentToken.length() > 0) {
                    tokens.add(currentToken.toString().trim());
                    currentToken = new StringBuilder();
                }
            } else {
                currentToken.append(c);
            }
        }

        if (currentToken.length() > 0) {
            tokens.add(currentToken.toString().trim());
        }

        return tokens;
    }

    /**
     * 增强：CreateIndex 转换为 OceanBase 索引语法（全局/本地索引）
     */
    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = cleanIdentifier(createIndex.getIndex().getName());
        String tableName = cleanIdentifier(createIndex.getTable().getName());
        boolean isUnique = createIndex.toString().toUpperCase().contains("UNIQUE") ||
                (indexName != null && indexName.toUpperCase().startsWith("UNIQUE_"));

        List<String> columns = new ArrayList<>();
        List<?> colsObj = null;
        try {
            colsObj = (List<?>)CreateIndex.class.getMethod("getColumns").invoke(createIndex);
        } catch (Exception e) {
            String idxStr = createIndex.toString();
            int lpar = idxStr.indexOf('(');
            int rpar = idxStr.indexOf(')', lpar);
            if (lpar != -1 && rpar != -1) {
                String inParens = idxStr.substring(lpar + 1, rpar);
                String[] colArr = inParens.split(",");
                for (String raw : colArr) {
                    String clean = raw.trim().replaceAll("[`'\"]", "");
                    if (!clean.isEmpty()) columns.add(cleanIdentifier(clean));
                }
            }
        }
        if (colsObj != null) {
            for (Object col : colsObj) {
                if (col instanceof Column) {
                    columns.add(cleanIdentifier(((Column) col).getColumnName()));
                } else if (col instanceof String) {
                    columns.add(cleanIdentifier((String) col));
                }
            }
        }

        // 获取 OceanBase 索引类型
        OBIndexType idxType = getIndexType(tableName, columns);

        oceanBaseSql.append("CREATE");
        if (isUnique) oceanBaseSql.append(" UNIQUE");
        oceanBaseSql.append(" INDEX ").append(indexName);

        // 追加 OceanBase 分布式索引类型
        if (idxType == OBIndexType.GLOBAL) {
            oceanBaseSql.append(" GLOBAL");
        } else if (idxType == OBIndexType.LOCAL) {
            oceanBaseSql.append(" LOCAL");
        }

        oceanBaseSql.append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(")");

        // OceanBase 索引存储类型（默认 BTREE）
        String indexStr = createIndex.toString();
        if (indexStr.toUpperCase().contains("USING BTREE")) {
            oceanBaseSql.append(" USING BTREE");
        } else if (indexStr.toUpperCase().contains("USING HASH")) {
            oceanBaseSql.append(" USING HASH");
        } else {
            oceanBaseSql.append(" USING BTREE");
        }

        oceanBaseSql.append(";\n\n");
    }

    @Override
    public void visit(Insert insert) {
        String tableName = cleanIdentifier(insert.getTable().getName());
        oceanBaseSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            oceanBaseSql.append(" (");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                oceanBaseSql.append(colName);
                if (i < columns.size() - 1) oceanBaseSql.append(", ");
            }
            oceanBaseSql.append(")");
        }

        String valuesStr = insert.toString().toUpperCase();
        int valuesIdx = valuesStr.indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = insert.toString().substring(valuesIdx + 6);
            valuesPart = valuesPart.replace("CURRENT_TIMESTAMP", "SYSDATE");
            valuesPart = replaceBooleanLiterals(valuesPart);
        }

        oceanBaseSql.append(" VALUES").append(valuesPart).append(";\n\n");
    }

    @Override
    public void visit(Update update) {
        String tableName = cleanIdentifier(update.getTable().getName());
        oceanBaseSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = valueExpr.replace("CURRENT_TIMESTAMP", "SYSDATE");
            valueExpr = replaceBooleanLiterals(valueExpr);
            valueExpr = processWhereColumnNames(valueExpr);
            oceanBaseSql.append(colName).append(" = ").append(valueExpr);
            if (i < cols.size() - 1) oceanBaseSql.append(", ");
        }

        oceanBaseSql.append(processWhereExpression(update.getWhere())).append(";\n\n");
    }

    @Override
    public void visit(Delete delete) {
        String tableName = cleanIdentifier(delete.getTable().getName());
        oceanBaseSql.append("DELETE FROM ").append(tableName);
        oceanBaseSql.append(processWhereExpression(delete.getWhere())).append(";\n\n");
    }

    /**
     * 处理 DROP TABLE IF EXISTS `xxx`
     */
    @Override
    public void visit(Drop drop) {
        // 只关心 DROP TABLE，其它类型直接输出
        String type = drop.getType();
        if (type == null || !"TABLE".equalsIgnoreCase(type)) {
            oceanBaseSql.append(drop.toString()).append(";\n\n");
            return;
        }

        String tableName;
        if (drop.getName() != null) {
            tableName = cleanIdentifier(drop.getName().getName());
        } else {
            tableName = drop.toString().replaceAll("(?i)DROP\\s+TABLE\\s+(IF\\s+EXISTS\\s+)?", "").trim();
            tableName = cleanIdentifier(tableName);
        }

        // Oracle 模式安全删除：忽略 ORA-00942
        oceanBaseSql.append("BEGIN\n")
                .append("  EXECUTE IMMEDIATE 'DROP TABLE ").append(tableName).append("';\n")
                .append("EXCEPTION\n")
                .append("  WHEN OTHERS THEN\n")
                .append("    IF SQLCODE != -942 THEN\n")
                .append("      RAISE;\n")
                .append("    END IF;\n")
                .append("END;\n/\n\n");
    }

    private static class IndexArtifacts {
        final List<String> constraints;
        final List<String> indexes;
        IndexArtifacts(List<String> constraints, List<String> indexes) {
            this.constraints = constraints;
            this.indexes = indexes;
        }
    }

    /**
     * 获取转换后的 OceanBase SQL
     */
    public String getOceanBaseSql() {
        return oceanBaseSql.toString();
    }
}
