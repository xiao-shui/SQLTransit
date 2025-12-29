package org.example.SqlTransit.tool;

import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.statement.create.table.Index;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MysqlToGDBVisitor extends StatementVisitorAdapter {
    private final StringBuilder goldenDbSql = new StringBuilder();
    private final Map<String, List<String>> tableShardingInfo = new HashMap<>();

    private static final Set<String> GOLDENDB_KEYWORDS = new HashSet<>(Arrays.asList(
            "SHARD", "SHARDKEY", "SHARDCOUNT", "DATANODE", "GROUP",
            "PARTITION", "PARTITIONBY", "HASH", "RANGE", "LIST",
            "SCHEMA", "GLOBAL", "LOCAL", "CLUSTER", "REPLICA",
            "SEQUENCE", "SHARDING", "DISTRIBUTED"
    ));

    // 新增：GoldenDB索引类型枚举
    private enum GDBIndexType {
        GLOBAL, LOCAL, NORMAL
    }

    private String cleanIdentifier(String name) {
        if (name == null) return null;
        String cleanName = name.replaceAll("^[`'\"]+|[`'\"]+$", "");

        if (GOLDENDB_KEYWORDS.contains(cleanName.toUpperCase()) ||
                !cleanName.matches("^[a-zA-Z_][a-zA-Z0-9_]*$")) {
            return "`" + cleanName + "`";
        }
        return cleanName;
    }

    private String replaceBooleanLiterals(String sql) {
        return sql;
    }

    private String processWhereColumnNames(String sql) {
        return sql;
    }

    private boolean isKeyword(String token) {
        return Arrays.asList("AND", "OR", "NOT", "IS", "IN", "LIKE", "BETWEEN",
                        "NULL", "EXISTS", "TRUE", "FALSE", "SELECT", "FROM",
                        "WHERE", "GROUP", "BY", "ORDER", "HAVING", "LIMIT",
                        "OFFSET", "UNION", "ALL", "DISTINCT", "SHARD",
                        "SHARDKEY", "PARTITION")
                .contains(token.toUpperCase());
    }

    private String processWhereExpression(Expression where) {
        if (where == null) return "";
        String expr = where.toString();
        expr = replaceBooleanLiterals(expr);
        expr = processWhereColumnNames(expr);
        return " WHERE " + expr;
    }

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
                    if (length > 16383) {
                        return "VARCHAR(16383)";
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
                return "TIMESTAMP";
            case "DATE":
                return "DATE";
            case "TIME":
                return "TIME";
            case "YEAR":
                return "YEAR";
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
                return "DECIMAL(10,2)";
            case "NUMERIC":
                if (args != null && args.size() >= 2) {
                    return "NUMERIC(" + args.get(0) + "," + args.get(1) + ")";
                }
                return "NUMERIC(10,2)";
            case "BIT":
                if (args != null && !args.isEmpty()) {
                    return "BIT(" + args.get(0) + ")";
                }
                return "BIT(1)";
            case "BOOL":
            case "BOOLEAN":
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
                return "JSON";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + argsToJoinedString(args) + ")";
                }
                return type;
        }
    }

    private void extractShardingInfo(CreateTable createTable, String tableName) {
        String createStr = createTable.toString().toUpperCase();

        Pattern shardKeyPattern = Pattern.compile("SHARDKEY\\s*\\(([^)]+)\\)", Pattern.CASE_INSENSITIVE);
        Matcher shardKeyMatcher = shardKeyPattern.matcher(createStr);

        if (shardKeyMatcher.find()) {
            String shardKeys = shardKeyMatcher.group(1);
            String[] keys = shardKeys.split(",");
            List<String> shardKeyList = new ArrayList<>();

            for (String key : keys) {
                String cleanKey = cleanIdentifier(key.trim());
                shardKeyList.add(cleanKey);
            }

            tableShardingInfo.put(tableName, shardKeyList);
        }
    }

    // 新增：判断索引类型（全局/本地）
    private GDBIndexType getIndexType(String tableName, List<String> indexColumns) {
        List<String> shardKeys = tableShardingInfo.get(tableName);
        if (shardKeys == null || shardKeys.isEmpty()) {
            return GDBIndexType.NORMAL;
        }
        // 若索引包含分片键，默认转为本地索引；否则转为全局索引
        for (String col : indexColumns) {
            if (shardKeys.contains(col)) {
                return GDBIndexType.LOCAL;
            }
        }
        return GDBIndexType.GLOBAL;
    }

    // 新增：处理CreateTable中的表级索引
    private void processTableIndexes(CreateTable createTable, String tableName) {
        try {
            // 反射获取CreateTable中的索引列表
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<Index> indexes = (List<Index>) getIndexesMethod.invoke(createTable);

            if (indexes != null && !indexes.isEmpty()) {
                for (Index idx : indexes) {
                    String idxName = cleanIdentifier(idx.getName());
                    if (idxName == null || idxName.isEmpty()) {
                        // 自动生成索引名
                        idxName = "idx_" + tableName + "_" + String.join("_", idx.getColumnsNames());
                    }

                    // Replaced idx.isUnique() and idx.isPrimary() with heuristics:
                    // isUnique: name contains "UK_" or "UNIQUE" (case-insensitive) or toString contains "UNIQUE"
                    boolean isUnique = false;
                    boolean isPrimary = false;
                    String idxNameRaw = idx.getName() != null ? idx.getName().toUpperCase() : "";
                    String idxStr = idx.toString().toUpperCase();

                    if (idxNameRaw.contains("UK_") || idxNameRaw.contains("UNIQUE") || idxStr.contains("UNIQUE")) {
                        isUnique = true;
                    }
                    // isPrimary: name contains "PK_" or "PRIMARY" or idx definition string contains "PRIMARY KEY"
                    if (idxNameRaw.contains("PK_") || idxNameRaw.contains("PRIMARY") || idxStr.contains("PRIMARY KEY")) {
                        isPrimary = true;
                    }

                    List<String> idxColumns = new ArrayList<>();
                    for (Object colObj : idx.getColumnsNames()) {
                        idxColumns.add(cleanIdentifier(colObj.toString()));
                    }

                    // 跳过主键索引（已在字段定义中处理）
                    if (isPrimary) {
                        continue;
                    }

                    // 获取GoldenDB索引类型
                    GDBIndexType idxType = getIndexType(tableName, idxColumns);

                    // 构建索引SQL
                    goldenDbSql.append("\n");
                    goldenDbSql.append("CREATE ");
                    if (isUnique) {
                        goldenDbSql.append("UNIQUE ");
                    }
                    goldenDbSql.append("INDEX ").append(idxName);
                    // 追加GoldenDB分布式索引类型
                    if (idxType == GDBIndexType.GLOBAL) {
                        goldenDbSql.append(" GLOBAL");
                    } else if (idxType == GDBIndexType.LOCAL) {
                        goldenDbSql.append(" LOCAL");
                    }
                    goldenDbSql.append(" ON ").append(tableName)
                            .append(" (").append(String.join(", ", idxColumns)).append(")");
                    // 补充索引存储类型（默认BTREE）
                    goldenDbSql.append(" USING BTREE;");
                }
            }
        } catch (Exception e) {
            // 兼容低版本JSqlParser
            String createStr = createTable.toString();
            Pattern indexPattern = Pattern.compile(
                    "(?i)(UNIQUE\\s+)?KEY\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE
            );
            Matcher idxMatcher = indexPattern.matcher(createStr);
            while (idxMatcher.find()) {
                boolean isUnique = idxMatcher.group(1) != null;
                String idxName = cleanIdentifier(idxMatcher.group(2));
                String columns = idxMatcher.group(3);
                String[] colArr = columns.split(",");
                List<String> idxColumns = new ArrayList<>();
                for (String col : colArr) {
                    idxColumns.add(cleanIdentifier(col.trim()));
                }

                GDBIndexType idxType = getIndexType(tableName, idxColumns);
                goldenDbSql.append("\n");
                goldenDbSql.append("CREATE ");
                if (isUnique) {
                    goldenDbSql.append("UNIQUE ");
                }
                goldenDbSql.append("INDEX ").append(idxName);
                if (idxType == GDBIndexType.GLOBAL) {
                    goldenDbSql.append(" GLOBAL");
                } else if (idxType == GDBIndexType.LOCAL) {
                    goldenDbSql.append(" LOCAL");
                }
                goldenDbSql.append(" ON ").append(tableName)
                        .append(" (").append(String.join(", ", idxColumns)).append(") USING BTREE;");
            }
        }
    }

    @Override
    public void visit(CreateTable createTable) {
        String tableName = cleanIdentifier(createTable.getTable().getName());

        extractShardingInfo(createTable, tableName);

        goldenDbSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) goldenDbSql.append(",\n");

            String colName = cleanIdentifier(col.getColumnName());
            String colType = convertColumnType(col.getColDataType().getDataType(),
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
            goldenDbSql.append("    ").append(colName).append(" ").append(colType);

            if (charset != null) {
                goldenDbSql.append(" CHARACTER SET ").append(charset);
            }
            if (collation != null) {
                goldenDbSql.append(" COLLATE ").append(collation);
            }

            if (isAutoIncrement) {
                goldenDbSql.append(" AUTO_INCREMENT");
            }

            if (defaultValStr != null) {
                defaultValStr = defaultValStr.trim();
                if (defaultValStr.contains("CURRENT_TIMESTAMP") ||
                        defaultValStr.contains("NOW()")) {
                    goldenDbSql.append(" DEFAULT CURRENT_TIMESTAMP");
                } else if (colType.contains("TINYINT(1)") &&
                        (defaultValStr.equalsIgnoreCase("true") ||
                                defaultValStr.equalsIgnoreCase("false"))) {
                    goldenDbSql.append(" DEFAULT ").append(defaultValStr.equalsIgnoreCase("true") ? "1" : "0");
                } else if (defaultValStr.startsWith("'") && defaultValStr.endsWith("'")) {
                    goldenDbSql.append(" DEFAULT ").append(defaultValStr);
                } else {
                    goldenDbSql.append(" DEFAULT ").append(defaultValStr);
                }
            }

            if (isNotNull) {
                goldenDbSql.append(" NOT NULL");
            }

            if (isPrimaryKey) {
                goldenDbSql.append(" PRIMARY KEY");
            }

            if (isUnique) {
                goldenDbSql.append(" UNIQUE");
            }

            // 字段注释直接放在字段定义后面
            if (columnComment != null && !columnComment.isEmpty()) {
                columnComment = columnComment.replaceAll("^['\"]|['\"]$", "");
                goldenDbSql.append(" COMMENT '").append(columnComment.replace("'", "''")).append("'");
            }
        }

        // 表级约束处理（外键、检查约束等）
        processTableLevelConstraints(createTable, tableName);

        goldenDbSql.append("\n)");

        // 表级注释
        String tableComment = extractTableComment(createTable);
        if (tableComment != null && !tableComment.isEmpty()) {
            tableComment = tableComment.trim();
            if (tableComment.startsWith("'") && tableComment.endsWith("'")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            } else if (tableComment.startsWith("\"") && tableComment.endsWith("\"")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            }
            tableComment = tableComment.replace("'", "''");
            goldenDbSql.append(" COMMENT='").append(tableComment).append("'");
        }

        // 表选项
        goldenDbSql.append(" ENGINE=InnoDB");
        goldenDbSql.append(" DEFAULT CHARSET=utf8mb4");
        goldenDbSql.append(" COLLATE=utf8mb4_general_ci");

        goldenDbSql.append(";\n");

        // 新增：处理表内索引（表级索引）
        processTableIndexes(createTable, tableName);
        goldenDbSql.append("\n");

        // 添加分片键语句
        List<String> shardKeys = tableShardingInfo.get(tableName);
        if (shardKeys != null && !shardKeys.isEmpty()) {
            goldenDbSql.append("ALTER TABLE ").append(tableName).append(" ADD SHARDKEY (");
            for (int i = 0; i < shardKeys.size(); i++) {
                if (i > 0) goldenDbSql.append(", ");
                goldenDbSql.append(shardKeys.get(i));
            }
            goldenDbSql.append(");\n\n");
        }
    }

    private void processTableLevelConstraints(CreateTable createTable, String tableName) {
        String createStr = createTable.toString();

        // 提取外键约束
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

            goldenDbSql.append(",\n    CONSTRAINT ").append(constraintName)
                    .append(" FOREIGN KEY (").append(columns).append(")")
                    .append(" REFERENCES ").append(refTable)
                    .append(" (").append(refColumns).append(")");
        }

        // 提取检查约束
        Pattern checkPattern = Pattern.compile(
                "(?i)CONSTRAINT\\s+([^\\s]+)\\s+CHECK\\s*\\(([^)]+)\\)",
                Pattern.CASE_INSENSITIVE
        );
        Matcher checkMatcher = checkPattern.matcher(createStr);

        while (checkMatcher.find()) {
            String constraintName = cleanIdentifier(checkMatcher.group(1));
            String condition = checkMatcher.group(2);

            goldenDbSql.append(",\n    CONSTRAINT ").append(constraintName)
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

            goldenDbSql.append(",\n    CONSTRAINT ").append(constraintName)
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

    // 增强：CreateIndex的转换逻辑，适配GoldenDB分布式索引
    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = cleanIdentifier(createIndex.getIndex().getName());
        String tableName = cleanIdentifier(createIndex.getTable().getName());
        // Remove use of .isUnique(); only use heuristics
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

        // 获取GoldenDB索引类型（全局/本地）
        GDBIndexType idxType = getIndexType(tableName, columns);

        goldenDbSql.append("CREATE");
        if (isUnique) goldenDbSql.append(" UNIQUE");
        goldenDbSql.append(" INDEX ").append(indexName);

        // 追加分布式索引类型
        if (idxType == GDBIndexType.GLOBAL) {
            goldenDbSql.append(" GLOBAL");
        } else if (idxType == GDBIndexType.LOCAL) {
            goldenDbSql.append(" LOCAL");
        }

        goldenDbSql.append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(")");

        // 补充索引存储引擎（默认BTREE，兼容MySQL）
        String indexStr = createIndex.toString();
        if (indexStr.toUpperCase().contains("USING BTREE")) {
            goldenDbSql.append(" USING BTREE");
        } else if (indexStr.toUpperCase().contains("USING HASH")) {
            goldenDbSql.append(" USING HASH");
        } else {
            goldenDbSql.append(" USING BTREE");
        }

        goldenDbSql.append(";\n\n");
    }

    @Override
    public void visit(Insert insert) {
        String tableName = cleanIdentifier(insert.getTable().getName());
        goldenDbSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            goldenDbSql.append(" (");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                goldenDbSql.append(colName);
                if (i < columns.size() - 1) goldenDbSql.append(", ");
            }
            goldenDbSql.append(")");
        }

        String valuesStr = insert.toString().toUpperCase();
        int valuesIdx = valuesStr.indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = insert.toString().substring(valuesIdx + 6);
            valuesPart = replaceBooleanLiterals(valuesPart);
        }

        goldenDbSql.append(" VALUES").append(valuesPart).append(";\n\n");
    }

    @Override
    public void visit(Update update) {
        String tableName = cleanIdentifier(update.getTable().getName());
        goldenDbSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = replaceBooleanLiterals(valueExpr);
            valueExpr = processWhereColumnNames(valueExpr);
            goldenDbSql.append(colName).append(" = ").append(valueExpr);
            if (i < cols.size() - 1) goldenDbSql.append(", ");
        }

        goldenDbSql.append(processWhereExpression(update.getWhere())).append(";\n\n");
    }

    @Override
    public void visit(Delete delete) {
        String tableName = cleanIdentifier(delete.getTable().getName());
        goldenDbSql.append("DELETE FROM ").append(tableName);
        goldenDbSql.append(processWhereExpression(delete.getWhere())).append(";\n\n");
    }

    public String getGoldenDBSql() {
        return goldenDbSql.toString();
    }
}