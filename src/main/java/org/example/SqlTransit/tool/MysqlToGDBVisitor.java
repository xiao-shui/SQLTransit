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

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MysqlToGDBVisitor extends StatementVisitorAdapter {
    private final StringBuilder goldenDbSql = new StringBuilder();
    private final List<String> comments = new ArrayList<>();
    private final Map<String, List<String>> tableShardingInfo = new HashMap<>();
    private final List<String> partitionStatements = new ArrayList<>();

    private static final Set<String> GOLDENDB_KEYWORDS = new HashSet<>(Arrays.asList(
            "SHARD", "SHARDKEY", "SHARDCOUNT", "DATANODE", "GROUP",
            "PARTITION", "PARTITIONBY", "HASH", "RANGE", "LIST",
            "SCHEMA", "GLOBAL", "LOCAL", "CLUSTER", "REPLICA",
            "SEQUENCE", "SHARDING", "DISTRIBUTED"
    ));

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

    private String joinListWithComma(List<?> list) {
        // Utility replacement for String.join(",", list) which is unavailable for List<?>
        if (list == null || list.isEmpty()) return "";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < list.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(list.get(i));
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
                    return "ENUM(" + joinListWithComma(args) + ")";
                }
                return "ENUM('Y','N')";
            case "SET":
                if (args != null && !args.isEmpty()) {
                    return "SET(" + joinListWithComma(args) + ")";
                }
                return "SET('')";
            case "JSON":
                return "JSON";
            case "GEOMETRY":
                return "GEOMETRY";
            case "POINT":
                return "POINT";
            case "LINESTRING":
                return "LINESTRING";
            case "POLYGON":
                return "POLYGON";
            case "MULTIPOINT":
                return "MULTIPOINT";
            case "MULTILINESTRING":
                return "MULTILINESTRING";
            case "MULTIPOLYGON":
                return "MULTIPOLYGON";
            case "GEOMETRYCOLLECTION":
                return "GEOMETRYCOLLECTION";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + joinListWithComma(args) + ")";
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
                        String fkConstraint = "CONSTRAINT FK_" + tableName + "_" + colName +
                                " FOREIGN KEY (" + colName + ")";
                        if (j + 4 < specs.size()) {
                            String refTable = specs.get(j + 2).replace("`", "").replace("\"", "");
                            String refCol = specs.get(j + 4).replace("`", "").replace("\"", "");
                            fkConstraint += " REFERENCES " + cleanIdentifier(refTable) +
                                    "(" + cleanIdentifier(refCol) + ")";
                        }
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
                    case "KEY":
                        if (j > 0 && "PRIMARY".equalsIgnoreCase(specs.get(j-1))) {
                        } else {
                        }
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
                    case "CHECK":
                        if (j + 1 < specs.size()) {
                            String checkExpr = specs.get(j + 1);
                            goldenDbSql.append(",\n    CONSTRAINT CHK_" + tableName + "_" + colName +
                                    " CHECK (" + checkExpr + ")");
                            j++;
                        }
                        break;
                }
            }

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
            } else if (!isPrimaryKey) {
                goldenDbSql.append(" NULL");
            }

            if (isPrimaryKey) {
                goldenDbSql.append(" PRIMARY KEY");
            }

            if (columnComment != null && !columnComment.isEmpty()) {
                columnComment = columnComment.replaceAll("^['\"]|['\"]$", "");
                comments.add("COMMENT ON COLUMN " + tableName + "." + colName +
                        " IS '" + columnComment.replace("'", "''") + "';\n");
            }
        }

        List<String> uniqueConstraints = extractUniqueConstraints(createTable);
        for (String uniqueConstraint : uniqueConstraints) {
            goldenDbSql.append(",\n    ").append(uniqueConstraint);
        }

        goldenDbSql.append("\n)");

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

        goldenDbSql.append(" ENGINE=InnoDB");
        goldenDbSql.append(" DEFAULT CHARSET=utf8mb4");
        goldenDbSql.append(" COLLATE=utf8mb4_general_ci");

        goldenDbSql.append(";\n\n");

        List<String> shardKeys = tableShardingInfo.get(tableName);
        if (shardKeys != null && !shardKeys.isEmpty()) {
            goldenDbSql.append("ALTER TABLE ").append(tableName).append(" ADD SHARDKEY (");
            for (int i = 0; i < shardKeys.size(); i++) {
                if (i > 0) goldenDbSql.append(", ");
                goldenDbSql.append(shardKeys.get(i));
            }
            goldenDbSql.append(");\n\n");
        }

        if (!comments.isEmpty()) {
            for (String cmt : comments) {
                goldenDbSql.append(cmt);
            }
            comments.clear();
        }
    }

    private List<String> extractUniqueConstraints(CreateTable createTable) {
        List<String> constraints = new ArrayList<>();
        String createStr = createTable.toString();

        Pattern uniquePattern = Pattern.compile(
                "(?i)(UNIQUE\\s+(?:KEY\\s+)?(?:`[^`]+`\\s+)?\\([^)]+\\))"
        );
        Matcher matcher = uniquePattern.matcher(createStr);

        while (matcher.find()) {
            constraints.add(matcher.group(1));
        }

        return constraints;
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

        goldenDbSql.append("CREATE");
        if (isUnique) goldenDbSql.append(" UNIQUE");
        goldenDbSql.append(" INDEX ").append(indexName)
                .append(" ON ").append(tableName)
                .append(" (").append(joinListWithCommaWithSpace(columns)).append(")");

        String indexStr = createIndex.toString();
        if (indexStr.toUpperCase().contains("USING BTREE")) {
            goldenDbSql.append(" USING BTREE");
        } else if (indexStr.toUpperCase().contains("USING HASH")) {
            goldenDbSql.append(" USING HASH");
        }

        goldenDbSql.append(";\n\n");
    }

    // Helper method for join in "CREATE INDEX ..." since standard String.join may not support List<?> for some compilers
    private String joinListWithCommaWithSpace(List<?> list) {
        if (list == null || list.isEmpty()) return "";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < list.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(list.get(i));
        }
        return sb.toString();
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