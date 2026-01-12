package org.example.SqlTransit.tool;


import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.drop.Drop;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.statement.alter.Alter;
import net.sf.jsqlparser.statement.alter.AlterExpression;
import net.sf.jsqlparser.statement.select.Select;
import net.sf.jsqlparser.statement.select.PlainSelect;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;

import java.lang.reflect.Method;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MysqlToOracleVisitor extends StatementVisitorAdapter {
    private final StringBuilder oracleSql = new StringBuilder();
    private final List<String> comments = new ArrayList<>(); // 用于保存要输出的COMMENT ON语句

    // 工具方法：清理标识符（去除引号并大写）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
    }

    // 工具方法：获取带模式名的完整表名（如果存在 schema，则保留：SCHEMA.TABLE）
    private String getFullTableName(Table table) {
        if (table == null) return null;
        String baseName = cleanIdentifier(table.getName());
        try {
            String schema = table.getSchemaName();
            if (schema != null && !schema.isEmpty()) {
                return cleanIdentifier(schema) + "." + baseName;
            }
        } catch (Exception ignore) {
        }
        return baseName;
    }

    // 工具方法：替换布尔字面量 true/false → Y/N（忽略字符串内）
    private String replaceBooleanLiterals(String sql) {
        StringBuilder sb = new StringBuilder();
        boolean inString = false;
        int i = 0;

        while (i < sql.length()) {
            char ch = sql.charAt(i);
            if (ch == '\'') {
                sb.append(ch);
                i++;
                // 跳过整个字符串
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
                // 匹配 true/false 单词
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

    // 工具方法：大写 WHERE 中的列名（跳过关键字和函数）
    private String uppercaseWhereColumnNames(String sql) {
        StringBuilder sb = new StringBuilder();
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

                // 检查是否是函数（紧跟 '('）
                boolean isFunc = end < sql.length() && sql.charAt(end) == '(';

                // SQL 关键字不转大写
                if (isKeyword(token)) {
                    sb.append(token);
                } else if (isFunc) {
                    sb.append(token);
                } else {
                    // 检查是否为 table.col 形式
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

    // 判断是否为 SQL 关键字
    private boolean isKeyword(String token) {
        return Arrays.asList("AND", "OR", "NOT", "IS", "IN", "LIKE", "BETWEEN", "NULL", "EXISTS", "TRUE", "FALSE")
                .contains(token.toUpperCase());
    }


    // 工具方法：生成主键约束名称（格式：pk_列名，小写）
    private String generatePrimaryKeyConstraintName(String tableName, List<String> primaryKeyCols) {
        if (primaryKeyCols == null || primaryKeyCols.isEmpty()) {
            return "pk_" + tableName.toLowerCase();
        }
        // 使用第一个列名生成约束名：pk_列名（小写）
        String firstCol = primaryKeyCols.get(0).toLowerCase();
        return "pk_" + firstCol;
    }

    // 工具方法：提取表的注释（获取CREATE TABLE末尾的COMMENT='xxx'）
    @SuppressWarnings("unchecked")
    private String extractTableComment(CreateTable createTable) {
        // 方法1：直接访问 tableOptionsStrings
        try {
            java.lang.reflect.Method getOptionsMethod = CreateTable.class.getMethod("getTableOptionsStrings");
            List<String> tableOptions = (List<String>) getOptionsMethod.invoke(createTable);

            if (tableOptions != null && !tableOptions.isEmpty()) {
                // 根据你提供的结构：["COMMENT", "=", "'用户基础信息表'"]
                // 查找 COMMENT 关键字
                for (int i = 0; i < tableOptions.size(); i++) {
                    String option = tableOptions.get(i);
                    if ("COMMENT".equalsIgnoreCase(option.trim())) {
                        // 检查后面是否有 = 号
                        if (i + 2 < tableOptions.size()) {
                            String nextOption = tableOptions.get(i + 1);
                            if ("=".equals(nextOption.trim())) {
                                // 返回注释内容（去掉可能的引号）
                                String comment = tableOptions.get(i + 2);
                                return comment.trim();
                            }
                        }
                        // 如果没有 = 号，直接取下一个作为注释
                        if (i + 1 < tableOptions.size()) {
                            String comment = tableOptions.get(i + 1);
                            return comment.trim();
                        }
                    }
                }

                // 如果没有找到 COMMENT 关键字，检查是否有 = 号连接的注释
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

                // 尝试直接查找包含单引号的内容作为注释
                for (String option : tableOptions) {
                    if ((option.contains("'") || option.contains("\"")) &&
                            option.length() > 2) { // 至少有一个字符加上两个引号
                        return option.trim();
                    }
                }
            }
        } catch (Exception e) {
            // 忽略异常，尝试其他方法
        }

        // 方法2：从 toString() 解析
        String createStr = createTable.toString();

        // 先检查常见的注释格式
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
                // 如果找到的注释包含引号，去掉它们
                if ((comment.startsWith("'") && comment.endsWith("'")) ||
                        (comment.startsWith("\"") && comment.endsWith("\""))) {
                    comment = comment.substring(1, comment.length() - 1);
                }
                return comment;
            }
        }

        // 方法3：检查是否存在注释相关的部分
        String[] lines = createStr.split("\n");
        for (String line : lines) {
            if (line.trim().toUpperCase().contains("COMMENT")) {
                String cleanLine = line.trim();
                int commentIndex = cleanLine.toUpperCase().indexOf("COMMENT");
                if (commentIndex != -1) {
                    String afterComment = cleanLine.substring(commentIndex + "COMMENT".length()).trim();
                    // 移除可能的 = 号
                    if (afterComment.startsWith("=")) {
                        afterComment = afterComment.substring(1).trim();
                    }
                    // 移除引号
                    if ((afterComment.startsWith("'") && afterComment.endsWith("'")) ||
                            (afterComment.startsWith("\"") && afterComment.endsWith("\""))) {
                        return afterComment.substring(1, afterComment.length() - 1);
                    }
                    return afterComment;
                }
            }
        }
        return null;
    }
    // 字段类型转换
    private String convertColumnType(String mysqlType, List<?> args) {
        String type = mysqlType.toUpperCase();
        switch (type) {
            case "INT":
                return "NUMBER(10)";
            case "VARCHAR":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR2(" + args.get(0) + ")";
                }
                return "VARCHAR2";
            case "DATETIME":
            case "TIMESTAMP":
                return "TIMESTAMP";
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
                return "NUMBER(32,0)";
            case "DECIMAL":
                return "NUMBER";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + args.get(0) + ")";
                }
                return type;
        }
    }

    @Override
    public void visit(Drop drop) {
        // 只关心 DROP TABLE，其它类型直接输出
        String type = drop.getType();
        if (type == null || !"TABLE".equalsIgnoreCase(type)) {
            oracleSql.append(drop.toString()).append(";\n\n");
            return;
        }

        String tableName;
        if (drop.getName() != null) {
            tableName = cleanIdentifier(drop.getName().getName());
        } else {
            tableName = drop.toString().replaceAll("(?i)DROP\\s+TABLE\\s+(IF\\s+EXISTS\\s+)?", "").trim();
            tableName = cleanIdentifier(tableName);
        }

        oracleSql.append("BEGIN\n" +
                "  EXECUTE IMMEDIATE 'DROP TABLE " + tableName + "';\n" +
                "EXCEPTION\n" +
                "  WHEN OTHERS THEN\n" +
                "    IF SQLCODE != -942 THEN\n" +
                "      RAISE;\n" +
                "    END IF;\n" +
                "END;\n\n");
    }

    // 处理 CREATE TABLE
    @Override
    public void visit(CreateTable createTable) {
        String tableName = getFullTableName(createTable.getTable());
        oracleSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();
        boolean hasColumnLevelPrimaryKey = false; // 记录是否有列级主键

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) oracleSql.append(",\n");

            String colName = cleanIdentifier(col.getColumnName());
            String colType = convertColumnType(col.getColDataType().getDataType(),
                    col.getColDataType().getArgumentsStringList());

            // 解析 column spec - 修复方法
            List<String> specs = new ArrayList<>();
            String fullColStr = col.toString();

            // 方法1：使用 getColumnSpecStrings (如果可用)
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
                // 方法2：改进的 toString 解析
                // 提取列定义部分（从列名开始到逗号或结尾）
                String pattern = Pattern.quote(col.getColumnName()) + "\\s+.*?(?=,\\s*|$)";
                Pattern r = Pattern.compile(pattern, Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                Matcher m = r.matcher(fullColStr);

                if (m.find()) {
                    String columnDef = m.group();

                    // 移除列名和数据类型，得到纯约束部分
                    String colNamePattern = Pattern.quote(col.getColumnName());
                    String dataTypePattern = Pattern.quote(col.getColDataType().getDataType());
                    String constraintsOnly = columnDef
                            .replaceFirst("^" + colNamePattern + "\\s+", "")
                            .replaceFirst("^" + dataTypePattern + "\\s*", "")
                            .trim();

                    // 智能解析约束（处理括号、引号等）
                    specs = parseConstraintTokens(constraintsOnly);
                }
            }

            // 新增：从列规格中解析约束（如果可用）
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
                // 忽略，不使用此方法
            }

            // 解析约束标志
            boolean isAutoIncrement = false, isPrimaryKey = false,
                    isNotNull = false, isUnique = false;
            String defaultValStr = null;
            String columnComment = null;

            // 支持 UNIQUE、NOT NULL 出现在不同次序、方式
            for (int j = 0; j < specs.size(); j++) {
                String spec = specs.get(j).toUpperCase().trim();

                // 检查两词组合
                if (j + 1 < specs.size()) {
                    String twoWordSpec = spec + " " + specs.get(j + 1).toUpperCase();
                    if ("PRIMARY KEY".equals(twoWordSpec)) {
                        isPrimaryKey = true;
                        j++; // 跳过 KEY
                        continue;
                    }
                    if ("NOT NULL".equals(twoWordSpec)) {
                        isNotNull = true;
                        j++; // 跳过 NULL
                        continue;
                    }
                }

                // 检查单词约束
                if ("AUTO_INCREMENT".equals(spec) || "AUTOINCREMENT".equals(spec)) {
                    isAutoIncrement = true;
                } else if ("PRIMARY".equals(spec)) {
                    // 单独的 PRIMARY 可能表示 PRIMARY KEY
                    isPrimaryKey = true;
                } else if ("KEY".equals(spec) && j > 0 && "PRIMARY".equalsIgnoreCase(specs.get(j-1))) {
                    // 已经处理过，跳过
                } else if ("NOT".equals(spec)) {
                    // 单独的 NOT 可能表示 NOT NULL
                    isNotNull = true;
                } else if ("NULL".equals(spec) && j > 0 && "NOT".equalsIgnoreCase(specs.get(j-1))) {
                    // 已经处理过，跳过
                } else if ("UNIQUE".equals(spec)) {
                    isUnique = true;
                } else if ("DEFAULT".equals(spec) && j + 1 < specs.size()) {
                    defaultValStr = specs.get(j + 1);
                    j++; // 跳过默认值
                } else if ("COMMENT".equals(spec) && j + 1 < specs.size()) {
                    columnComment = specs.get(j + 1);
                    j++; // 跳过注释内容
                }
            }

            // 从原始列定义字符串中直接提取 DEFAULT 后面的完整表达式，尽量保留原始写法
            String extractedDefault = null;
            if (fullColStr != null) {
                Pattern defaultPattern = Pattern.compile(
                        "(?i)DEFAULT\\s+([^\\s]+(?:\\s+[^\\s]+)*?)(?=\\s+(?:COMMENT|PRIMARY|UNIQUE|NOT|NULL|CHECK|,|$))",
                        Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                Matcher defaultMatcher = defaultPattern.matcher(fullColStr);
                if (defaultMatcher.find()) {
                    extractedDefault = defaultMatcher.group(1).trim();
                }
            }
            String finalDefaultVal = extractedDefault != null ? extractedDefault : defaultValStr;

            // 构建字段定义
            oracleSql.append("    ").append(colName).append(" ").append(colType);

            if (isAutoIncrement) {
                oracleSql.append(" GENERATED BY DEFAULT AS IDENTITY");
            }

            if (finalDefaultVal != null) {
                // 处理特殊默认值
                String dv = finalDefaultVal.trim();
                String upperDefault = dv.toUpperCase(Locale.ROOT);

                // MySQL 中的 DEFAULT NULL 在 Oracle 中去除（不生成默认值）
                if (!"NULL".equals(upperDefault) && !"'NULL'".equals(upperDefault) && !"\"NULL\"".equals(upperDefault)) {
                    if (upperDefault.contains("CURRENT_TIMESTAMP")) {
                        oracleSql.append(" DEFAULT SYSDATE");
                    } else if (colType.equalsIgnoreCase("VARCHAR2(1)") &&
                            (dv.equalsIgnoreCase("true") || dv.equalsIgnoreCase("false"))) {
                        oracleSql.append(" DEFAULT '").append(dv.equalsIgnoreCase("true") ? "Y" : "N").append("'");
                    } else if (dv.startsWith("'") && dv.endsWith("'")) {
                        // 带引号的字符串
                        oracleSql.append(" DEFAULT ").append(dv);
                    } else {
                        // 数字或其他值
                        oracleSql.append(" DEFAULT ").append(dv);
                    }
                }
            } else if (colType.equalsIgnoreCase("VARCHAR2(1)")) {
                oracleSql.append(" DEFAULT 'Y'");
            }

            // 约束顺序：主键 > 唯一 > 非空
            if (isPrimaryKey) {
                oracleSql.append(" PRIMARY KEY");
                hasColumnLevelPrimaryKey = true; // 标记已有列级主键
            } else {
                if (isUnique) {
                    oracleSql.append(" UNIQUE");
                }
                if (isNotNull) {
                    oracleSql.append(" NOT NULL");
                }
            }

            // 处理字段注释
            if (columnComment != null && !columnComment.isEmpty()) {
                // 移除可能的引号
                columnComment = columnComment.replaceAll("^['\"]|['\"]$", "");
                comments.add("COMMENT ON COLUMN " + tableName + "." + colName +
                        " IS '" + columnComment.replace("'", "''") + "';\n");
            }

        }

        // 处理表级 PRIMARY KEY（如果列级没有主键）
        List<String> tablePrimaryKeyCols = new ArrayList<>();
        if (!hasColumnLevelPrimaryKey) {
            try {
                java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
                List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
                if (indexes != null) {
                    for (Object idx : indexes) {
                        String idxStr = idx.toString().trim().toUpperCase();
                        if (idxStr.contains("PRIMARY KEY")) {
                            // 尝试获取列名
                            try {
                                java.lang.reflect.Method getColumnsNamesMethod = idx.getClass().getMethod("getColumnsNames");
                                Object pkColsObj = getColumnsNamesMethod.invoke(idx);
                                if (pkColsObj instanceof List) {
                                    for (Object colObj : (List<?>) pkColsObj) {
                                        String colName = cleanIdentifier(colObj.toString());
                                        tablePrimaryKeyCols.add(colName);
                                    }
                                }
                            } catch (Exception e) {
                                // 如果反射失败，尝试从字符串解析
                                Pattern pkPattern = Pattern.compile(
                                        "PRIMARY KEY\\s*\\(([^)]+)\\)", Pattern.CASE_INSENSITIVE);
                                Matcher m = pkPattern.matcher(idxStr);
                                if (m.find()) {
                                    String cols = m.group(1);
                                    String[] colArr = cols.split(",");
                                    for (String col : colArr) {
                                        tablePrimaryKeyCols.add(cleanIdentifier(col.trim()));
                                    }
                                }
                            }
                            break; // 只处理第一个主键约束
                        }
                    }
                }
            } catch (Exception e) {
                // 如果反射失败，尝试从 toString() 解析
                String createStr = createTable.toString();
                Pattern pkPattern = Pattern.compile(
                        "PRIMARY KEY\\s*\\(([^)]+)\\)", Pattern.CASE_INSENSITIVE);
                Matcher m = pkPattern.matcher(createStr);
                if (m.find()) {
                    String cols = m.group(1);
                    String[] colArr = cols.split(",");
                    for (String col : colArr) {
                        tablePrimaryKeyCols.add(cleanIdentifier(col.trim()));
                    }
                }
            }

            // 如果有表级主键，添加到 CREATE TABLE 中（使用CONSTRAINT格式）
            if (!tablePrimaryKeyCols.isEmpty()) {
                String pkConstraintName = generatePrimaryKeyConstraintName(tableName, tablePrimaryKeyCols);
                oracleSql.append(",\n    CONSTRAINT ").append(pkConstraintName)
                        .append(" PRIMARY KEY (").append(String.join(", ", tablePrimaryKeyCols)).append(")");
            }
        }

        oracleSql.append("\n);\n\n");

        // 处理表级索引（在 CREATE TABLE 之后生成单独的 CREATE INDEX 语句）
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
            if (indexes != null && !indexes.isEmpty()) {
                for (Object idx : indexes) {
                    String idxStr = idx.toString().trim();
                    String idxStrUpper = idxStr.toUpperCase();

                    // 跳过主键索引（已经在 CREATE TABLE 中处理）
                    if (idxStrUpper.contains("PRIMARY KEY")) {
                        continue;
                    }

                    // 判断是否是唯一索引
                    boolean isUnique = idxStrUpper.contains("UNIQUE");
                    String idxName = null;
                    List<String> idxColumns = new ArrayList<>();

                    // 尝试获取索引名和列名
                    try {
                        java.lang.reflect.Method getNameMethod = idx.getClass().getMethod("getName");
                        Object nameObj = getNameMethod.invoke(idx);
                        if (nameObj != null) {
                            idxName = cleanIdentifier(nameObj.toString());
                        }
                    } catch (Exception e) {
                        // 忽略
                    }

                    try {
                        java.lang.reflect.Method getColumnsNamesMethod = idx.getClass().getMethod("getColumnsNames");
                        Object colsObj = getColumnsNamesMethod.invoke(idx);
                        if (colsObj instanceof List) {
                            for (Object colObj : (List<?>) colsObj) {
                                idxColumns.add(cleanIdentifier(colObj.toString()));
                            }
                        }
                    } catch (Exception e) {
                        // 如果反射失败，尝试从字符串解析
                        Pattern indexPattern = Pattern.compile(
                                "(?:UNIQUE\\s+)?(?:KEY|INDEX)\\s+(?:[`'\"]?\\w+[`'\"]?\\s+)?\\(([^)]+)\\)",
                                Pattern.CASE_INSENSITIVE);
                        Matcher m = indexPattern.matcher(idxStr);
                        if (m.find()) {
                            String cols = m.group(1);
                            String[] colArr = cols.split(",");
                            for (String col : colArr) {
                                idxColumns.add(cleanIdentifier(col.trim()));
                            }
                        }
                    }

                    // 如果没有获取到索引名，尝试从字符串解析
                    if (idxName == null || idxName.isEmpty()) {
                        Pattern namePattern = Pattern.compile(
                                "(?:UNIQUE\\s+)?(?:KEY|INDEX)\\s+([`'\"]?\\w+[`'\"]?)",
                                Pattern.CASE_INSENSITIVE);
                        Matcher m = namePattern.matcher(idxStr);
                        if (m.find()) {
                            idxName = cleanIdentifier(m.group(1));
                        } else {
                            // 如果没有索引名，生成一个默认名称
                            idxName = "IDX_" + tableName + "_" + String.join("_", idxColumns);
                        }
                    }

                    // 如果成功获取到列名，生成 CREATE INDEX 语句
                    if (!idxColumns.isEmpty()) {
                        oracleSql.append("CREATE");
                        if (isUnique) {
                            oracleSql.append(" UNIQUE");
                        }
                        oracleSql.append(" INDEX ").append(idxName)
                                .append(" ON ").append(tableName)
                                .append(" (").append(String.join(", ", idxColumns)).append(");\n\n");
                    }
                }
            }
        } catch (Exception e) {
            // 如果反射失败，尝试从 toString() 解析索引
            String createStr = createTable.toString();
            Pattern indexPattern = Pattern.compile(
                    "(?i)(UNIQUE\\s+)?(?:KEY|INDEX)\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE);
            Matcher idxMatcher = indexPattern.matcher(createStr);
            while (idxMatcher.find()) {
                boolean isUnique = idxMatcher.group(1) != null;
                String idxName = cleanIdentifier(idxMatcher.group(2));
                String indexColumns = idxMatcher.group(3);
                String[] colArr = indexColumns.split(",");
                List<String> idxColumns = new ArrayList<>();
                for (String col : colArr) {
                    idxColumns.add(cleanIdentifier(col.trim()));
                }

                // 跳过主键索引
                if (idxName.toUpperCase().contains("PRIMARY")) {
                    continue;
                }

                oracleSql.append("CREATE");
                if (isUnique) {
                    oracleSql.append(" UNIQUE");
                }
                oracleSql.append(" INDEX ").append(idxName)
                        .append(" ON ").append(tableName)
                        .append(" (").append(String.join(", ", idxColumns)).append(");\n\n");
            }
        }

        // 表级注释处理 - 修复方法
        String tableComment = extractTableComment(createTable);
        if (tableComment != null && !tableComment.isEmpty()) {
            // 确保注释字符串格式正确
            tableComment = tableComment.trim();
            // 移除可能的多余引号
            if (tableComment.startsWith("'") && tableComment.endsWith("'")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            } else if (tableComment.startsWith("\"") && tableComment.endsWith("\"")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            }
            // 转义单引号
            tableComment = tableComment.replace("'", "''");
            comments.add("COMMENT ON TABLE " + tableName + " IS '" + tableComment + "';\n");
        }

        // 添加所有comment语句（表及字段）
        if (!comments.isEmpty()) {
            for (String cmt : comments) {
                oracleSql.append(cmt);
            }
            comments.clear();
        }
    }

    // 辅助方法：智能解析约束令牌
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

        // 添加最后一个token
        if (currentToken.length() > 0) {
            tokens.add(currentToken.toString().trim());
        }

        return tokens;
    }


    // 辅助方法：解析并连接列名
    private String parseAndJoinCols(String cols) {
        if (cols == null) return "";
        String[] arr = cols.split(",");
        List<String> result = new ArrayList<>();
        for (String c : arr) {
            result.add(cleanIdentifier(c.trim()));
        }
        return String.join(", ", result);
    }

    // 处理 CREATE INDEX
    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = cleanIdentifier(createIndex.getIndex().getName());
        String tableName;
        try {
            Table table = createIndex.getTable();
            if (table != null && table.getSchemaName() != null && !table.getSchemaName().isEmpty()) {
                tableName = cleanIdentifier(table.getSchemaName()) + "." + cleanIdentifier(table.getName());
            } else {
                tableName = cleanIdentifier(createIndex.getTable().getName());
            }
        } catch (Exception e) {
            tableName = cleanIdentifier(createIndex.getTable().getName());
        }

        boolean isUnique = false;
        try {
            Method isUniqueMethod = createIndex.getClass().getMethod("isUnique");
            Object result = isUniqueMethod.invoke(createIndex);
            if (result instanceof Boolean) {
                isUnique = (Boolean) result;
            }
        } catch (Exception e) {
            String text = createIndex.toString().toUpperCase();
            if (text.contains("UNIQUE") || (indexName != null && indexName.toUpperCase().contains("UNIQUE"))) {
                isUnique = true;
            }
        }

        // getColumns() 不存在时，尝试解析 toString()
        List<String> columns = new ArrayList<>();
        List<?> colsObj = null;
        try {
            colsObj = (List<?>)CreateIndex.class.getMethod("getColumns").invoke(createIndex);
        } catch (Exception e) {
            // getColumns() 方法不存在，尝试解析 SQL 字符串
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

        oracleSql.append("CREATE");
        if (isUnique) oracleSql.append(" UNIQUE");
        oracleSql.append(" INDEX ").append(indexName)
                .append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(");\n\n");
    }

    @Override
    public void visit(Alter alter) {
        String tableName = null;
        String alterStr = alter.toString();
        try {
            Method getTableMethod = Alter.class.getMethod("getTable");
            Object tblObj = getTableMethod.invoke(alter);
            if (tblObj != null && tblObj.getClass().getMethod("getName") != null) {
                Table tableObj = (Table)tblObj;
                if (tableObj.getSchemaName() != null && !tableObj.getSchemaName().isEmpty()) {
                    tableName = cleanIdentifier(tableObj.getSchemaName()) + "." + cleanIdentifier(tableObj.getName());
                } else {
                    tableName = cleanIdentifier(tableObj.getName());
                }
            }
        } catch (Exception e) {
            Pattern p = Pattern.compile("ALTER TABLE\\s+((\"[^\"]+\"\\.)?\"[^\"]+\"|`[^`]+`|[\\w]+)", Pattern.CASE_INSENSITIVE);
            Matcher m = p.matcher(alterStr);
            if (m.find()) {
                String t = m.group(1);
                t = t.replaceAll("[`'\"]+", "");
                tableName = cleanIdentifier(t);
            }
            if (tableName == null) {
                Pattern p2 = Pattern.compile("ALTER TABLE\\s+([\\w\\[\\]]+)", Pattern.CASE_INSENSITIVE);
                Matcher m2 = p2.matcher(alterStr);
                if (m2.find()) {
                    tableName = cleanIdentifier(m2.group(1));
                }
            }
        }
        if (tableName == null) {
            tableName = "UNKNOWN_TABLE";
        }
        
        // 先尝试从 AlterExpression 解析
        List<AlterExpression> expressions = null;
        try {
            Method getAlterExprMethod = Alter.class.getMethod("getAlterExpressions");
            Object alterExprsObj = getAlterExprMethod.invoke(alter);
            if (alterExprsObj instanceof List) {
                @SuppressWarnings("unchecked")
                List<AlterExpression> alterExprs = (List<AlterExpression>) alterExprsObj;
                expressions = alterExprs;
            }
        } catch (Exception e) {}
        
        if (expressions != null) {
            for (AlterExpression expr : expressions) {
                if (expr == null) continue;
                String opStr = expr.getOperation() != null ? expr.getOperation().toString().toUpperCase() : "";
                if ("ADD".equals(opStr) && expr.getIndex() != null) {
                    Object idx = expr.getIndex();
                    String idxStr = idx.toString();
                    StringBuilder sb = new StringBuilder();
                    
                    Pattern pkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*PRIMARY KEY\\s*\\(([^)]+)\\)",
                            Pattern.CASE_INSENSITIVE);
                    Matcher pkMatcher = pkPattern.matcher(idxStr);
                    if (pkMatcher.find()) {
                        String pkName = pkMatcher.group(1) == null ? "" : pkMatcher.group(1);
                        String cols = pkMatcher.group(2);
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (pkName != null && !pkName.isEmpty()) {
                            sb.append(cleanIdentifier(pkName)).append(" ");
                        }
                        sb.append("PRIMARY KEY (")
                                .append(parseAndJoinCols(cols))
                                .append(");\n\n");
                        oracleSql.append(sb.toString());
                        continue;
                    }
                    
                    Pattern uqPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*UNIQUE\\s*\\(([^)]+)\\)",
                            Pattern.CASE_INSENSITIVE);
                    Matcher uqMatcher = uqPattern.matcher(idxStr);
                    if (uqMatcher.find()) {
                        String uqName = uqMatcher.group(1) == null ? "" : uqMatcher.group(1);
                        String cols = uqMatcher.group(2);
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (uqName != null && !uqName.isEmpty()) {
                            sb.append(cleanIdentifier(uqName)).append(" ");
                        }
                        sb.append("UNIQUE (")
                                .append(parseAndJoinCols(cols))
                                .append(");\n\n");
                        oracleSql.append(sb.toString());
                        continue;
                    }
                    
                    Pattern fkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"][^`'\"]+[`'\"]|[\\w_]+)?\\s*FOREIGN\\s+KEY\\s*\\(([^)]+)\\)\\s*REFERENCES\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
                            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                    Matcher fkMatcher = fkPattern.matcher(idxStr);
                    if (fkMatcher.find()) {
                        String fkName = fkMatcher.group(1) == null ? "" : fkMatcher.group(1);
                        String localCols = fkMatcher.group(2);
                        String refTable = fkMatcher.group(3);
                        String refCols = fkMatcher.group(4);
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (fkName != null && !fkName.trim().isEmpty()) {
                            sb.append(cleanIdentifier(fkName.trim())).append(" ");
                        }
                        sb.append("FOREIGN KEY (")
                                .append(parseAndJoinCols(localCols))
                                .append(") REFERENCES ")
                                .append(cleanIdentifier(refTable.replaceAll("[`'\"]", "")))
                                .append(" (")
                                .append(parseAndJoinCols(refCols))
                                .append(");\n\n");
                        oracleSql.append(sb.toString());
                        continue;
                    }
                    
                    Pattern checkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*CHECK\\s*\\((.+)\\)", Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                    Matcher checkMatcher = checkPattern.matcher(idxStr);
                    if (checkMatcher.find()) {
                        String checkName = checkMatcher.group(1) == null ? "" : checkMatcher.group(1);
                        String checkExpr = checkMatcher.group(2).trim();
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (checkName != null && !checkName.isEmpty()) {
                            sb.append(cleanIdentifier(checkName)).append(" ");
                        }
                        sb.append("CHECK (").append(checkExpr).append(");\n\n");
                        oracleSql.append(sb.toString());
                        continue;
                    }
                }
            }
        } else {
            String s = alter.toString();
            oracleSql.append(s).append(";\n\n");
        }
        
        // 如果 AlterExpression 解析失败，尝试直接从 alter.toString() 解析
        if (expressions == null || expressions.isEmpty()) {
            // 解析 ADD CONSTRAINT PRIMARY KEY
            Pattern pkPattern = Pattern.compile(
                    "ADD\\s+CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*PRIMARY KEY\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE);
            Matcher pkMatcher = pkPattern.matcher(alterStr);
            if (pkMatcher.find()) {
                String pkName = pkMatcher.group(1);
                String cols = pkMatcher.group(2);
                StringBuilder sb = new StringBuilder();
                sb.append("ALTER TABLE ").append(tableName)
                        .append(" ADD CONSTRAINT ");
                if (pkName != null && !pkName.trim().isEmpty()) {
                    sb.append(cleanIdentifier(pkName)).append(" ");
                }
                sb.append("PRIMARY KEY (")
                        .append(parseAndJoinCols(cols))
                        .append(");\n\n");
                oracleSql.append(sb.toString());
                return;
            }
            
            // 解析 ADD CONSTRAINT UNIQUE
            Pattern uqPattern = Pattern.compile(
                    "ADD\\s+CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*UNIQUE\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE);
            Matcher uqMatcher = uqPattern.matcher(alterStr);
            if (uqMatcher.find()) {
                String uqName = uqMatcher.group(1);
                String cols = uqMatcher.group(2);
                StringBuilder sb = new StringBuilder();
                sb.append("ALTER TABLE ").append(tableName)
                        .append(" ADD CONSTRAINT ");
                if (uqName != null && !uqName.trim().isEmpty()) {
                    sb.append(cleanIdentifier(uqName)).append(" ");
                }
                sb.append("UNIQUE (")
                        .append(parseAndJoinCols(cols))
                        .append(");\n\n");
                oracleSql.append(sb.toString());
                return;
            }
            
            // 解析 ADD INDEX
            Pattern indexPattern = Pattern.compile(
                    "ADD\\s+(UNIQUE\\s+)?INDEX\\s+([`'\"]?\\w+[`'\"]?)\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE);
            Matcher indexMatcher = indexPattern.matcher(alterStr);
            if (indexMatcher.find()) {
                boolean isUnique = indexMatcher.group(1) != null;
                String idxName = cleanIdentifier(indexMatcher.group(2));
                String cols = indexMatcher.group(3);
                
                StringBuilder sb = new StringBuilder();
                sb.append("CREATE");
                if (isUnique) sb.append(" UNIQUE");
                sb.append(" INDEX ").append(idxName)
                        .append(" ON ").append(tableName)
                        .append(" (").append(parseAndJoinCols(cols))
                        .append(");\n\n");
                oracleSql.append(sb.toString());
                return;
            }
            
            // 解析 ADD CONSTRAINT FOREIGN KEY
            Pattern fkPattern = Pattern.compile(
                    "ADD\\s+CONSTRAINT\\s+([`'\"][^`'\"]+[`'\"]|[\\w_]+)?\\s*FOREIGN\\s+KEY\\s*\\(([^)]+)\\)\\s*REFERENCES\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
            Matcher fkMatcher = fkPattern.matcher(alterStr);
            if (fkMatcher.find()) {
                String fkName = fkMatcher.group(1);
                String localCols = fkMatcher.group(2);
                String refTable = fkMatcher.group(3);
                String refCols = fkMatcher.group(4);
                StringBuilder sb = new StringBuilder();
                sb.append("ALTER TABLE ").append(tableName)
                        .append(" ADD CONSTRAINT ");
                if (fkName != null && !fkName.trim().isEmpty()) {
                    sb.append(cleanIdentifier(fkName.trim())).append(" ");
                }
                sb.append("FOREIGN KEY (")
                        .append(parseAndJoinCols(localCols))
                        .append(") REFERENCES ")
                        .append(cleanIdentifier(refTable.replaceAll("[`'\"]", "")))
                        .append(" (")
                        .append(parseAndJoinCols(refCols))
                        .append(");\n\n");
                oracleSql.append(sb.toString());
                return;
            }
            
            // 解析 ADD CONSTRAINT CHECK
            Pattern checkPattern = Pattern.compile(
                    "ADD\\s+CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*CHECK\\s*\\((.+?)\\)",
                    Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
            Matcher checkMatcher = checkPattern.matcher(alterStr);
            if (checkMatcher.find()) {
                String checkName = checkMatcher.group(1);
                String checkExpr = checkMatcher.group(2).trim();
                StringBuilder sb = new StringBuilder();
                sb.append("ALTER TABLE ").append(tableName)
                        .append(" ADD CONSTRAINT ");
                if (checkName != null && !checkName.trim().isEmpty()) {
                    sb.append(cleanIdentifier(checkName)).append(" ");
                }
                sb.append("CHECK (").append(checkExpr).append(");\n\n");
                oracleSql.append(sb.toString());
                return;
            }
        }
        
        // 如果都无法解析，直接输出原始语句
        oracleSql.append(alterStr).append(";\n\n");
    }

    // 工具方法：转换 MySQL 函数为 Oracle 函数
    private String convertMysqlFunctions(String sql) {
        if (sql == null) return "";
        String result = sql;
        // NOW() -> SYSDATE
        result = result.replaceAll("(?i)\\bNOW\\s*\\(\\s*\\)", "SYSDATE");
        // CURRENT_TIMESTAMP -> SYSDATE
        result = result.replaceAll("(?i)\\bCURRENT_TIMESTAMP\\b", "SYSDATE");
        // IFNULL -> NVL
        result = result.replaceAll("(?i)\\bIFNULL\\s*\\(", "NVL(");
        // INTERVAL 转换（MySQL: INTERVAL 1 YEAR，Oracle: NUMTODSINTERVAL 或 INTERVAL '1' YEAR）
        result = result.replaceAll("(?i)INTERVAL\\s+(\\d+)\\s+YEAR", "INTERVAL '$1' YEAR");
        result = result.replaceAll("(?i)INTERVAL\\s+(\\d+)\\s+MONTH", "INTERVAL '$1' MONTH");
        result = result.replaceAll("(?i)INTERVAL\\s+(\\d+)\\s+DAY", "INTERVAL '$1' DAY");
        result = result.replaceAll("(?i)INTERVAL\\s+(\\d+)\\s+HOUR", "INTERVAL '$1' HOUR");
        result = result.replaceAll("(?i)INTERVAL\\s+(\\d+)\\s+MINUTE", "INTERVAL '$1' MINUTE");
        result = result.replaceAll("(?i)INTERVAL\\s+(\\d+)\\s+SECOND", "INTERVAL '$1' SECOND");
        return result;
    }

    // 处理 INSERT
    @Override
    public void visit(Insert insert) {
        String tableName = getFullTableName(insert.getTable());
        List<Column> columns = insert.getColumns();
        
        // 生成列名部分（如果有）
        StringBuilder columnPart = new StringBuilder();
        if (columns != null && !columns.isEmpty()) {
            columnPart.append(" (");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                columnPart.append(colName);
                if (i < columns.size() - 1) columnPart.append(", ");
            }
            columnPart.append(")");
        }

        // 尝试从 Insert 对象获取 Values
        try {
            Method getValuesMethod = Insert.class.getMethod("getValues");
            Object valuesObj = getValuesMethod.invoke(insert);
            
            if (valuesObj != null) {
                // 处理 ExpressionList（单行或多行）
                List<List<Expression>> valueRows = extractInsertValueRows(valuesObj);
                
                if (valueRows != null && !valueRows.isEmpty()) {
                    // 如果是多行插入，为每一行生成一个独立的 INSERT 语句
                    for (int i = 0; i < valueRows.size(); i++) {
                        List<Expression> rowExprs = valueRows.get(i);
                        oracleSql.append("INSERT INTO ").append(tableName).append(columnPart);
                        oracleSql.append(" VALUES (");
                        
                        for (int j = 0; j < rowExprs.size(); j++) {
                            if (j > 0) oracleSql.append(", ");
                            String exprStr = rowExprs.get(j).toString();
                            exprStr = convertMysqlFunctions(exprStr);
                            exprStr = replaceBooleanLiterals(exprStr);
                            oracleSql.append(exprStr);
                        }
                        
                        oracleSql.append(");\n");
                    }
                    oracleSql.append("\n");
                    return;
                }
            }
        } catch (Exception e) {
            // 如果反射失败，尝试从 toString() 解析
        }
        
        // 回退：从 toString() 解析（单行或多行）
        String insertStr = insert.toString();
        int valuesIdx = insertStr.toUpperCase().indexOf("VALUES");
        if (valuesIdx != -1) {
            String valuesPart = insertStr.substring(valuesIdx + 6).trim();
            valuesPart = convertMysqlFunctions(valuesPart);
            valuesPart = replaceBooleanLiterals(valuesPart);
            
            // 检查是否是多行插入（包含多个括号对）
            if (isMultiRowInsert(valuesPart)) {
                // 解析多行值
                List<String> valueRows = parseMultiRowValues(valuesPart);
                for (String valueRow : valueRows) {
                    oracleSql.append("INSERT INTO ").append(tableName).append(columnPart);
                    oracleSql.append(" VALUES ").append(valueRow).append(";\n");
                }
                oracleSql.append("\n");
                return;
            }
            
            // 单行插入
            oracleSql.append("INSERT INTO ").append(tableName).append(columnPart);
            oracleSql.append(" VALUES ").append(valuesPart);
        } else {
            // 无法解析，使用原始格式
            oracleSql.append("INSERT INTO ").append(tableName).append(columnPart);
        }

        oracleSql.append(";\n\n");
    }

    // 辅助方法：从 valuesObj 中提取多行值
    @SuppressWarnings("unchecked")
    private List<List<Expression>> extractInsertValueRows(Object valuesObj) {
        if (valuesObj == null) return null;
        
        try {
            // 尝试获取 getExpressions() 方法
            Method getExprsMethod = valuesObj.getClass().getMethod("getExpressions");
            Object exprsObj = getExprsMethod.invoke(valuesObj);
            
            if (exprsObj instanceof List) {
                List<Expression> expressions = (List<Expression>) exprsObj;
                
                if (expressions.isEmpty()) {
                    return null;
                }
                
                // 检查是否是多行插入（第一个元素以括号开头，可能是 ParenthesedExpressionList）
                String firstExprStr = expressions.get(0).toString().trim();
                if (firstExprStr.startsWith("(")) {
                    // 多行插入：每个元素是一行
                    List<List<Expression>> rows = new ArrayList<>();
                    for (Expression expr : expressions) {
                        // 尝试从每个 Expression 中提取表达式列表
                        try {
                            Method getExprsInExpr = expr.getClass().getMethod("getExpressions");
                            Object innerExprsObj = getExprsInExpr.invoke(expr);
                            if (innerExprsObj instanceof List) {
                                rows.add((List<Expression>) innerExprsObj);
                            } else {
                                // 如果不是列表，可能是单个表达式，创建单元素列表
                                List<Expression> singleRow = new ArrayList<>();
                                singleRow.add(expr);
                                rows.add(singleRow);
                            }
                        } catch (Exception e) {
                            // 无法获取内部表达式，尝试将整个表达式作为单个值
                            // 这种情况需要从字符串解析
                            String exprStr = expr.toString();
                            // 解析括号内的值：('Bob', 'bob@example.com')
                            List<Expression> row = parseExpressionListFromString(exprStr);
                            if (row != null && !row.isEmpty()) {
                                rows.add(row);
                            }
                        }
                    }
                    return rows.isEmpty() ? null : rows;
                } else {
                    // 单行插入：所有表达式组成一行
                    List<List<Expression>> rows = new ArrayList<>();
                    rows.add(expressions);
                    return rows;
                }
            }
        } catch (Exception e) {
            // 如果解析失败，返回 null，让调用者使用 toString() 解析
        }
        
        return null;
    }
    
    // 辅助方法：从字符串解析表达式列表（简单实现，主要用于回退）
    private List<Expression> parseExpressionListFromString(String exprStr) {
        // 这是一个简化实现，实际应该使用 JSQLParser 来解析
        // 这里返回 null，让调用者使用其他方法
        return null;
    }
    
    // 辅助方法：检查是否是多行插入
    private boolean isMultiRowInsert(String valuesPart) {
        if (valuesPart == null || valuesPart.trim().isEmpty()) {
            return false;
        }
        
        // 简单判断：如果包含 "), (" 模式，很可能是多行插入
        Pattern multiRowPattern = Pattern.compile("\\)\\s*,\\s*\\(");
        return multiRowPattern.matcher(valuesPart).find();
    }
    
    // 辅助方法：解析多行值字符串
    private List<String> parseMultiRowValues(String valuesPart) {
        List<String> rows = new ArrayList<>();
        
        if (valuesPart == null || valuesPart.trim().isEmpty()) {
            return rows;
        }
        
        // 使用正则表达式或手动解析，将 "('val1', 'val2'), ('val3', 'val4')" 
        // 分割成 ["('val1', 'val2')", "('val3', 'val4')"]
        
        List<String> result = new ArrayList<>();
        StringBuilder current = new StringBuilder();
        int depth = 0;
        boolean inString = false;
        char stringChar = 0;
        int startPos = -1;
        
        for (int i = 0; i < valuesPart.length(); i++) {
            char c = valuesPart.charAt(i);
            
            if (!inString && (c == '\'' || c == '"')) {
                inString = true;
                stringChar = c;
                if (depth == 0 && startPos == -1) {
                    startPos = i;
                }
                current.append(c);
            } else if (inString && c == stringChar && (i == 0 || valuesPart.charAt(i-1) != '\\')) {
                inString = false;
                current.append(c);
            } else if (!inString && c == '(') {
                if (depth == 0) {
                    startPos = i;
                    current = new StringBuilder();
                }
                depth++;
                current.append(c);
            } else if (!inString && c == ')') {
                current.append(c);
                depth--;
                if (depth == 0) {
                    // 找到一个完整的值行
                    String row = current.toString().trim();
                    if (!row.isEmpty()) {
                        result.add(row);
                    }
                    current = new StringBuilder();
                    startPos = -1;
                    // 跳过可能的逗号和空格
                    while (i + 1 < valuesPart.length() && 
                           (valuesPart.charAt(i + 1) == ',' || 
                            Character.isWhitespace(valuesPart.charAt(i + 1)))) {
                        i++;
                    }
                }
            } else {
                current.append(c);
            }
        }
        
        // 如果还有剩余的内容（单行插入的情况）
        if (depth == 0 && current.length() > 0) {
            String row = current.toString().trim();
            if (!row.isEmpty()) {
                result.add(row);
            }
        }
        
        return result.isEmpty() ? Arrays.asList(valuesPart.trim()) : result;
    }

    // 处理 UPDATE
    @Override
    @SuppressWarnings("deprecation")
    public void visit(Update update) {
        String tableName = getFullTableName(update.getTable());
        oracleSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        @SuppressWarnings("unchecked")
        List<Expression> exprs = (List<Expression>) (List<?>) update.getExpressions();
        
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            Expression expr = exprs.get(i);
            String valueExpr = convertExpression(expr);
            oracleSql.append(colName).append(" = ").append(valueExpr);
            if (i < cols.size() - 1) oracleSql.append(", ");
        }

        Expression where = update.getWhere();
        if (where != null) {
            String whereStr = convertExpression(where);
            oracleSql.append(" WHERE ").append(whereStr);
        }

        oracleSql.append(";\n\n");
    }

    // 辅助方法：转换表达式（处理 MySQL 函数、布尔值、列名等）
    private String convertExpression(Expression expr) {
        if (expr == null) return "";
        
        String exprStr = expr.toString();
        
        // 转换 MySQL 函数为 Oracle 函数
        exprStr = convertMysqlFunctions(exprStr);
        
        // 替换布尔值
        exprStr = replaceBooleanLiterals(exprStr);
        
        // 转换列名为大写（跳过字符串和函数）
        exprStr = uppercaseWhereColumnNames(exprStr);
        
        return exprStr;
    }

    // 处理 DELETE
    @Override
    public void visit(Delete delete) {
        String tableName = getFullTableName(delete.getTable());
        oracleSql.append("DELETE FROM ").append(tableName);
        
        Expression where = delete.getWhere();
        if (where != null) {
            String whereStr = convertExpression(where);
            oracleSql.append(" WHERE ").append(whereStr);
        }
        
        oracleSql.append(";\n\n");
    }

    // 处理 SELECT
    @Override
    @SuppressWarnings("deprecation")
    public void visit(Select select) {
        if (select.getSelectBody() instanceof PlainSelect) {
            PlainSelect plainSelect = (PlainSelect) select.getSelectBody();
            
            // 处理 SELECT 列表
            oracleSql.append("SELECT ");
            if (plainSelect.getSelectItems() != null) {
                boolean first = true;
                for (Object item : plainSelect.getSelectItems()) {
                    if (!first) oracleSql.append(", ");
                    String itemStr = item.toString();
                    // 转换列名为大写
                    itemStr = uppercaseWhereColumnNames(itemStr);
                    oracleSql.append(itemStr);
                    first = false;
                }
            } else {
                oracleSql.append("*");
            }
            
            // 处理 FROM
            if (plainSelect.getFromItem() != null) {
                String fromStr = plainSelect.getFromItem().toString();
                // 转换表名为大写，保留 schema
                if (plainSelect.getFromItem() instanceof Table) {
                    Table table = (Table) plainSelect.getFromItem();
                    fromStr = getFullTableName(table);
                } else {
                    fromStr = uppercaseWhereColumnNames(fromStr);
                }
                oracleSql.append(" FROM ").append(fromStr);
            }
            
            // 处理 WHERE
            if (plainSelect.getWhere() != null) {
                String whereStr = convertExpression(plainSelect.getWhere());
                oracleSql.append(" WHERE ").append(whereStr);
            }
            
            // 处理 ORDER BY
            if (plainSelect.getOrderByElements() != null) {
                oracleSql.append(" ORDER BY ");
                boolean first = true;
                for (Object orderElem : plainSelect.getOrderByElements()) {
                    if (!first) oracleSql.append(", ");
                    String orderStr = orderElem.toString();
                    orderStr = uppercaseWhereColumnNames(orderStr);
                    oracleSql.append(orderStr);
                    first = false;
                }
            }
            
            // 处理 LIMIT -> ROWNUM 或 FETCH FIRST
            if (plainSelect.getLimit() != null) {
                try {
                    Object limitObj = plainSelect.getLimit();
                    Method getRowCountMethod = limitObj.getClass().getMethod("getRowCount");
                    Object rowCountObj = getRowCountMethod.invoke(limitObj);
                    
                    long rowCount = 0;
                    if (rowCountObj instanceof LongValue) {
                        rowCount = ((LongValue) rowCountObj).getValue();
                    } else if (rowCountObj instanceof Long) {
                        rowCount = (Long) rowCountObj;
                    } else if (rowCountObj != null) {
                        rowCount = Long.parseLong(rowCountObj.toString());
                    }
                    
                    if (rowCount > 0) {
                        // 检查是否有 OFFSET
                        try {
                            Method getOffsetMethod = limitObj.getClass().getMethod("getOffset");
                            Object offsetObj = getOffsetMethod.invoke(limitObj);
                            long offset = 0;
                            if (offsetObj instanceof LongValue) {
                                offset = ((LongValue) offsetObj).getValue();
                            } else if (offsetObj instanceof Long) {
                                offset = (Long) offsetObj;
                            } else if (offsetObj != null) {
                                offset = Long.parseLong(offsetObj.toString());
                            }
                            
                            if (offset > 0) {
                                // Oracle 12c+ 使用 OFFSET ... ROWS FETCH NEXT ... ROWS ONLY
                                oracleSql.append(" OFFSET ").append(offset).append(" ROWS FETCH NEXT ").append(rowCount).append(" ROWS ONLY");
                            } else {
                                // 使用 FETCH FIRST ... ROWS ONLY (Oracle 12c+)
                                oracleSql.append(" FETCH FIRST ").append(rowCount).append(" ROWS ONLY");
                            }
                        } catch (Exception e) {
                            // 没有 OFFSET，使用 FETCH FIRST
                            oracleSql.append(" FETCH FIRST ").append(rowCount).append(" ROWS ONLY");
                        }
                    }
                } catch (Exception e) {
                    // 如果解析失败，尝试使用 ROWNUM 方式（Oracle 11g 及以下）
                    String limitStr = plainSelect.getLimit().toString();
                    // 简单提取数字
                    java.util.regex.Pattern limitPattern = Pattern.compile("LIMIT\\s+(\\d+)", Pattern.CASE_INSENSITIVE);
                    java.util.regex.Matcher limitMatcher = limitPattern.matcher(limitStr);
                    if (limitMatcher.find()) {
                        long rowCount = Long.parseLong(limitMatcher.group(1));
                        oracleSql.append(" FETCH FIRST ").append(rowCount).append(" ROWS ONLY");
                    }
                }
            }
            
            oracleSql.append(";\n\n");
        } else {
            // 非 PlainSelect，直接转换
            String selectStr = select.toString();
            selectStr = convertMysqlFunctions(selectStr);
            selectStr = replaceBooleanLiterals(selectStr);
            selectStr = uppercaseWhereColumnNames(selectStr);
            oracleSql.append(selectStr).append(";\n\n");
        }
    }

    // 获取最终 Oracle SQL
    public String getOracleSql() {
        return oracleSql.toString();
    }
}
