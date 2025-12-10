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

public class MysqlToPostgresqlVisitor extends StatementVisitorAdapter {
    private final StringBuilder postgresqlSql = new StringBuilder();
    private final List<String> comments = new ArrayList<>(); // 用于保存要输出的COMMENT ON语句

    // 工具方法：清理标识符（去除引号并小写）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[`'\"]+|[`'\"]+$", "").toLowerCase();
    }

    // 工具方法：处理MySQL特定的函数和语法
    private String convertMysqlFunctions(String sql) {
        String result = sql;

        // 函数转换
        result = result.replaceAll("(?i)CURRENT_TIMESTAMP\\(\\)", "CURRENT_TIMESTAMP");
        result = result.replaceAll("(?i)NOW\\(\\)", "CURRENT_TIMESTAMP");
        result = result.replaceAll("(?i)\\bIFNULL\\(", "COALESCE(");
        result = result.replaceAll("(?i)\\bISNULL\\(", "COALESCE(");

        // 替换LIMIT语法（需要更复杂的处理）
        result = result.replaceAll("(?i)LIMIT\\s+(\\d+)\\s*,\\s*(\\d+)", "LIMIT $2 OFFSET $1");

        // 替换字符串函数
        result = result.replaceAll("(?i)\\bCONCAT\\(", "\\|\\|");

        // 替换DATETIME为TIMESTAMP
        result = result.replaceAll("(?i)DATETIME", "TIMESTAMP");

        // 替换反引号为双引号
        result = result.replace("`", "\"");

        return result;
    }

    // 工具方法：处理 WHERE 条件表达式
    private String processWhereExpression(Expression where) {
        if (where == null) return "";
        String expr = where.toString();
        expr = convertMysqlFunctions(expr);
        return " WHERE " + expr;
    }


    // 工具方法：提取表的注释
    private String extractTableComment(CreateTable createTable) {
        // 方法1：直接访问 tableOptionsStrings
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
                    if ((option.contains("'") || option.contains("\"")) &&
                            option.length() > 2) {
                        return option.trim();
                    }
                }
            }
        } catch (Exception e) {
            // 忽略异常
        }

        // 方法2：从 toString() 解析
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

    // 字段类型转换 - MySQL转PostgreSQL
    private String convertColumnType(String mysqlType, List<?> args) {
        String type = mysqlType.toUpperCase();

        // 解析参数
        List<String> argList = new ArrayList<>();
        if (args != null) {
            for (Object arg : args) {
                if (arg != null) {
                    argList.add(arg.toString());
                }
            }
        }

        switch (type) {
            case "INT":
            case "INTEGER":
                return "INTEGER";
            case "SMALLINT":
                return "SMALLINT";
            case "TINYINT":
                if (!argList.isEmpty() && "1".equals(argList.get(0))) {
                    return "BOOLEAN";
                }
                return "SMALLINT";
            case "MEDIUMINT":
                return "INTEGER";
            case "BIGINT":
                return "BIGINT";
            case "VARCHAR":
                if (!argList.isEmpty()) {
                    int length = Integer.parseInt(argList.get(0));
                    if (length > 10485760) {
                        return "TEXT";
                    }
                    return "VARCHAR(" + argList.get(0) + ")";
                }
                return "VARCHAR(255)";
            case "CHAR":
                if (!argList.isEmpty()) {
                    return "CHAR(" + argList.get(0) + ")";
                }
                return "CHAR(1)";
            case "TEXT":
            case "LONGTEXT":
            case "MEDIUMTEXT":
            case "TINYTEXT":
                return "TEXT";
            case "DATETIME":
                return "TIMESTAMP";
            case "TIMESTAMP":
                return "TIMESTAMP";
            case "DATE":
                return "DATE";
            case "TIME":
                return "TIME";
            case "YEAR":
                return "INTEGER";
            case "FLOAT":
                if (argList.size() >= 2) {
                    return "REAL";
                }
                return "REAL";
            case "DOUBLE":
            case "DOUBLE PRECISION":
                return "DOUBLE PRECISION";
            case "DECIMAL":
            case "NUMERIC":
                if (argList.size() >= 2) {
                    return "NUMERIC(" + argList.get(0) + "," + argList.get(1) + ")";
                } else if (!argList.isEmpty()) {
                    return "NUMERIC(" + argList.get(0) + ")";
                }
                return "NUMERIC";
            case "BOOLEAN":
            case "BOOL":
                return "BOOLEAN";
            case "BLOB":
            case "LONGBLOB":
            case "MEDIUMBLOB":
            case "TINYBLOB":
                return "BYTEA";
            case "BINARY":
            case "VARBINARY":
                return "BYTEA";
            case "ENUM":
                return "VARCHAR(255)";
            case "SET":
                return "VARCHAR(255)";
            case "JSON":
                return "JSONB";
            case "GEOMETRY":
            case "POINT":
            case "LINESTRING":
            case "POLYGON":
                return type;
            case "UUID":
                return "UUID";
            case "SERIAL":
                return "SERIAL";
            case "BIGSERIAL":
                return "BIGSERIAL";
            case "BIT":
                if (!argList.isEmpty()) {
                    int bitLength = Integer.parseInt(argList.get(0));
                    if (bitLength == 1) {
                        return "BOOLEAN";
                    } else if (bitLength <= 8) {
                        return "SMALLINT";
                    } else if (bitLength <= 16) {
                        return "INTEGER";
                    } else {
                        return "BIGINT";
                    }
                }
                return "BIT VARYING";
            default:
                return "TEXT";
        }
    }

    // 处理 CREATE TABLE
    @Override
    public void visit(CreateTable createTable) {
        String tableName = cleanIdentifier(createTable.getTable().getName());
        postgresqlSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) postgresqlSql.append(",\n");

            String colName = cleanIdentifier(col.getColumnName());
            String colType = convertColumnType(col.getColDataType().getDataType(),
                    col.getColDataType().getArgumentsStringList());

            // 解析 column spec
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

            // 解析约束标志
            boolean isAutoIncrement = false, isPrimaryKey = false,
                    isNotNull = false, isUnique = false;
            String defaultValStr = null;
            String columnComment = null;

            for (int j = 0; j < specs.size(); j++) {
                String spec = specs.get(j).toUpperCase().trim();

                // 检查两词组合
                if (j + 1 < specs.size()) {
                    String twoWordSpec = spec + " " + specs.get(j + 1).toUpperCase();
                    if ("PRIMARY KEY".equals(twoWordSpec)) {
                        isPrimaryKey = true;
                        j++;
                        continue;
                    }
                    if ("NOT NULL".equals(twoWordSpec)) {
                        isNotNull = true;
                        j++;
                        continue;
                    }
                }

                // 检查单词约束
                if ("AUTO_INCREMENT".equals(spec) || "AUTOINCREMENT".equals(spec)) {
                    isAutoIncrement = true;
                } else if ("PRIMARY".equals(spec)) {
                    isPrimaryKey = true;
                } else if ("KEY".equals(spec) && j > 0 && "PRIMARY".equalsIgnoreCase(specs.get(j-1))) {
                    // 跳过
                } else if ("NOT".equals(spec)) {
                    isNotNull = true;
                } else if ("NULL".equals(spec) && j > 0 && "NOT".equalsIgnoreCase(specs.get(j-1))) {
                    // 跳过
                } else if ("UNIQUE".equals(spec)) {
                    isUnique = true;
                } else if ("DEFAULT".equals(spec) && j + 1 < specs.size()) {
                    defaultValStr = specs.get(j + 1);
                    j++;
                } else if ("COMMENT".equals(spec) && j + 1 < specs.size()) {
                    columnComment = specs.get(j + 1);
                    j++;
                }
            }

            // 构建字段定义
            postgresqlSql.append("    ").append(colName).append(" ").append(colType);

            // 处理AUTO_INCREMENT - PostgreSQL使用SERIAL或IDENTITY
            if (isAutoIncrement) {
                if (colType.equalsIgnoreCase("INTEGER") || colType.equalsIgnoreCase("INT")) {
                    postgresqlSql.append(" GENERATED BY DEFAULT AS IDENTITY");
                } else if (colType.equalsIgnoreCase("BIGINT")) {
                    postgresqlSql.append(" GENERATED BY DEFAULT AS IDENTITY");
                } else {
                    postgresqlSql.append(" /* AUTO_INCREMENT not fully supported for this type */");
                }
            }

            // 处理默认值
            if (defaultValStr != null) {
                defaultValStr = defaultValStr.trim();

                // MySQL的CURRENT_TIMESTAMP函数
                if (defaultValStr.toUpperCase().contains("CURRENT_TIMESTAMP") ||
                        defaultValStr.toUpperCase().contains("NOW()")) {
                    postgresqlSql.append(" DEFAULT CURRENT_TIMESTAMP");
                }
                // MySQL的布尔值处理
                else if (colType.equalsIgnoreCase("BOOLEAN")) {
                    if (defaultValStr.equals("'Y'") || defaultValStr.equals("'y'") ||
                            defaultValStr.equals("'1'") || defaultValStr.equals("1")) {
                        postgresqlSql.append(" DEFAULT TRUE");
                    } else if (defaultValStr.equals("'N'") || defaultValStr.equals("'n'") ||
                            defaultValStr.equals("'0'") || defaultValStr.equals("0")) {
                        postgresqlSql.append(" DEFAULT FALSE");
                    } else {
                        postgresqlSql.append(" DEFAULT ").append(defaultValStr);
                    }
                }
                // 处理MySQL的NULL
                else if (defaultValStr.equalsIgnoreCase("NULL")) {
                    postgresqlSql.append(" DEFAULT NULL");
                }
                // 其他情况
                else {
                    postgresqlSql.append(" DEFAULT ").append(defaultValStr);
                }
            }

            // 约束顺序
            if (isPrimaryKey) {
                postgresqlSql.append(" PRIMARY KEY");
            } else {
                if (isUnique) {
                    postgresqlSql.append(" UNIQUE");
                }
                if (isNotNull) {
                    postgresqlSql.append(" NOT NULL");
                }
            }

            // 处理字段注释 - PostgreSQL使用COMMENT ON语法
            if (columnComment != null && !columnComment.isEmpty()) {
                columnComment = columnComment.replaceAll("^['\"]|['\"]$", "");
                comments.add("COMMENT ON COLUMN " + tableName + "." + colName +
                        " IS '" + columnComment.replace("'", "''") + "';\n");
            }
        }

        postgresqlSql.append("\n);\n\n");

        // 表级注释处理
        String tableComment = extractTableComment(createTable);
        if (tableComment != null && !tableComment.isEmpty()) {
            tableComment = tableComment.trim();
            if (tableComment.startsWith("'") && tableComment.endsWith("'")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            } else if (tableComment.startsWith("\"") && tableComment.endsWith("\"")) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            }
            tableComment = tableComment.replace("'", "''");
            comments.add("COMMENT ON TABLE " + tableName + " IS '" + tableComment + "';\n");
        }

        // 添加所有comment语句
        if (!comments.isEmpty()) {
            for (String cmt : comments) {
                postgresqlSql.append(cmt);
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

        if (currentToken.length() > 0) {
            tokens.add(currentToken.toString().trim());
        }

        return tokens;
    }

    // 处理 CREATE INDEX
    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = cleanIdentifier(createIndex.getIndex().getName());
        String tableName = cleanIdentifier(createIndex.getTable().getName());
        boolean isUnique = createIndex.toString().toUpperCase().contains("UNIQUE") ||
                (indexName != null && indexName.startsWith("UNIQUE_"));

        List<String> columns = new ArrayList<>();
        List<?> colsObj = null;
        try {
            colsObj = (List<?>)CreateIndex.class.getMethod("getColumns").invoke(createIndex);
        } catch (Exception e) {
            // 解析 SQL 字符串
            String idxStr = createIndex.toString();
            int lpar = idxStr.indexOf('(');
            int rpar = idxStr.indexOf(')', lpar);
            if (lpar != -1 && rpar != -1) {
                String inParens = idxStr.substring(lpar + 1, rpar);
                String[] colArr = inParens.split(",");
                for (String raw : colArr) {
                    String clean = raw.trim().replaceAll("[`'\"]", "");
                    if (!clean.isEmpty()) columns.add(clean.toLowerCase());
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

        postgresqlSql.append("CREATE");
        if (isUnique) postgresqlSql.append(" UNIQUE");
        postgresqlSql.append(" INDEX ").append(indexName)
                .append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(");\n\n");
    }

    // 处理 INSERT
    @Override
    public void visit(Insert insert) {
        String tableName = cleanIdentifier(insert.getTable().getName());
        postgresqlSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            postgresqlSql.append("(");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                postgresqlSql.append(colName);
                if (i < columns.size() - 1) postgresqlSql.append(", ");
            }
            postgresqlSql.append(")");
        }

        // 获取VALUES部分并转换
        String valuesStr = insert.toString();
        int valuesIdx = valuesStr.toUpperCase().indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = valuesStr.substring(valuesIdx + 6);
            valuesPart = convertMysqlFunctions(valuesPart);
        }

        postgresqlSql.append(" VALUES").append(valuesPart).append(";\n\n");
    }

    // 处理 UPDATE
    @Override
    public void visit(Update update) {
        String tableName = cleanIdentifier(update.getTable().getName());
        postgresqlSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = convertMysqlFunctions(valueExpr);
            postgresqlSql.append(colName).append("=").append(valueExpr);
            if (i < cols.size() - 1) postgresqlSql.append(", ");
        }

        postgresqlSql.append(processWhereExpression(update.getWhere())).append(";\n\n");
    }

    // 处理 DELETE
    @Override
    public void visit(Delete delete) {
        String tableName = cleanIdentifier(delete.getTable().getName());
        postgresqlSql.append("DELETE FROM ").append(tableName);
        postgresqlSql.append(processWhereExpression(delete.getWhere())).append(";\n\n");
    }

    // 获取最终 PostgreSQL SQL
    public String getPostgresqlSql() {
        return postgresqlSql.toString();
    }

    // 清空缓冲区
    public void clear() {
        postgresqlSql.setLength(0);
        comments.clear();
    }
}