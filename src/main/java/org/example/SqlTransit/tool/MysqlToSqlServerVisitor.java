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

public class MysqlToSqlServerVisitor extends StatementVisitorAdapter {
    private final StringBuilder sqlServerSql = new StringBuilder();
    private final List<String> comments = new ArrayList<>(); // 用于保存要输出的COMMENT语句
    private final Map<String, List<String>> tableConstraints = new HashMap<>(); // 存储表级约束

    // 工具方法：清理标识符（SQL Server使用方括号）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        String cleanName = name.replaceAll("^[`'\"]+|[`'\"]+$", "");
        // SQL Server 标识符规则：首字符必须是字母、下划线、@或#，后续可以是字母数字、下划线、@、$、#
        if (!cleanName.matches("^[a-zA-Z_@#][a-zA-Z0-9_@$#]*$") ||
                cleanName.toUpperCase().matches("^(SELECT|INSERT|UPDATE|DELETE|CREATE|DROP|ALTER|WHERE|FROM)$")) {
            return "[" + cleanName + "]";
        }
        return cleanName;
    }

    // 工具方法：替换布尔字面量 true/false → 1/0
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
                    sb.append("1");
                    i += 4;
                    continue;
                }
                if (i + 5 <= sql.length() && sql.substring(i, i + 5).equalsIgnoreCase("false") &&
                        (i == 0 || !Character.isLetterOrDigit(sql.charAt(i - 1))) &&
                        (i + 5 == sql.length() || !Character.isLetterOrDigit(sql.charAt(i + 5)))) {
                    sb.append("0");
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
                        String tname = cleanIdentifier(token);
                        String cname = cleanIdentifier(sql.substring(end + 1, dotEnd));
                        sb.append(tname).append('.').append(cname);
                        i = dotEnd;
                        continue;
                    }
                    sb.append(cleanIdentifier(token));
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
        return Arrays.asList("AND", "OR", "NOT", "IS", "IN", "LIKE", "BETWEEN",
                        "NULL", "EXISTS", "TRUE", "FALSE", "SELECT", "FROM",
                        "WHERE", "GROUP", "BY", "ORDER", "HAVING")
                .contains(token.toUpperCase());
    }

    // 工具方法：处理 WHERE 条件表达式
    private String processWhereExpression(Expression where) {
        if (where == null) return "";
        String expr = where.toString();
        expr = expr.replace("CURRENT_TIMESTAMP", "GETDATE()");
        expr = expr.replace("NOW()", "GETDATE()");
        expr = replaceBooleanLiterals(expr);
        expr = uppercaseWhereColumnNames(expr);
        return " WHERE " + expr;
    }

    // 工具方法：提取表的注释
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
            // 忽略异常
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

    // 字段类型转换 (MySQL → SQL Server)
    private String convertColumnType(String mysqlType, List<?> args) {
        String type = mysqlType.toUpperCase();
        switch (type) {
            case "INT":
                return "INT";
            case "VARCHAR":
                if (args != null && !args.isEmpty()) {
                    Object arg = args.get(0);
                    if ("MAX".equals(arg.toString().toUpperCase())) {
                        return "VARCHAR(MAX)";
                    }
                    return "VARCHAR(" + arg + ")";
                }
                return "VARCHAR(255)";
            case "CHAR":
                if (args != null && !args.isEmpty()) {
                    return "CHAR(" + args.get(0) + ")";
                }
                return "CHAR(1)";
            case "TEXT":
                return "VARCHAR(MAX)";
            case "LONGTEXT":
            case "MEDIUMTEXT":
            case "TINYTEXT":
                return "VARCHAR(MAX)";
            case "DATETIME":
                return "DATETIME";
            case "TIMESTAMP":
                return "DATETIME2";
            case "DATE":
                return "DATE";
            case "TIME":
                return "TIME";
            case "YEAR":
                return "INT";
            case "TINYINT":
                return "TINYINT";
            case "SMALLINT":
                return "SMALLINT";
            case "MEDIUMINT":
                return "INT";
            case "BIGINT":
                return "BIGINT";
            case "BIT":
                return "BIT";
            case "BOOLEAN":
            case "BOOL":
                return "BIT";
            case "FLOAT":
                if (args != null && args.size() >= 2) {
                    return "FLOAT(" + args.get(0) + "," + args.get(1) + ")";
                }
                return "FLOAT";
            case "DOUBLE":
                return "FLOAT(53)";
            case "DECIMAL":
                if (args != null && args.size() >= 2) {
                    return "DECIMAL(" + args.get(0) + "," + args.get(1) + ")";
                } else if (args != null && !args.isEmpty()) {
                    return "DECIMAL(" + args.get(0) + ",0)";
                }
                return "DECIMAL(18,2)";
            case "NUMERIC":
                if (args != null && args.size() >= 2) {
                    return "NUMERIC(" + args.get(0) + "," + args.get(1) + ")";
                }
                return "NUMERIC(18,2)";
            case "BLOB":
            case "LONGBLOB":
            case "MEDIUMBLOB":
            case "TINYBLOB":
                return "VARBINARY(MAX)";
            case "BINARY":
                return "BINARY";
            case "VARBINARY":
                if (args != null && !args.isEmpty()) {
                    Object arg = args.get(0);
                    if ("MAX".equals(arg.toString().toUpperCase())) {
                        return "VARBINARY(MAX)";
                    }
                    return "VARBINARY(" + arg + ")";
                }
                return "VARBINARY(MAX)";
            case "ENUM":
            case "SET":
                return "VARCHAR(255)";
            case "JSON":
                return "NVARCHAR(MAX)";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + args.get(0) + ")";
                }
                return type;
        }
    }

    // 处理 CREATE TABLE
    @Override
    public void visit(CreateTable createTable) {
        String tableName = cleanIdentifier(createTable.getTable().getName());
        tableConstraints.put(tableName, new ArrayList<>());

        sqlServerSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) sqlServerSql.append(",\n");

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
                // 忽略
            }

            boolean isAutoIncrement = false, isPrimaryKey = false,
                    isNotNull = false, isUnique = false;
            String defaultValStr = null;
            String columnComment = null;
            String checkConstraint = null;

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
                    if ("FOREIGN KEY".equals(twoWordSpec)) {
                        // 外键约束暂存，稍后处理
                        String fkConstraint = "CONSTRAINT FK_" + tableName + "_" + colName + " FOREIGN KEY (" + colName + ")";
                        if (j + 4 < specs.size()) {
                            String refTable = specs.get(j + 2).replace("`", "").replace("\"", "");
                            String refCol = specs.get(j + 4).replace("`", "").replace("\"", "");
                            fkConstraint += " REFERENCES " + cleanIdentifier(refTable) + "(" + cleanIdentifier(refCol) + ")";
                        }
                        tableConstraints.get(tableName).add(fkConstraint);
                        j += 4; // 跳过 FOREIGN KEY (table(column))
                        continue;
                    }
                }

                if ("AUTO_INCREMENT".equals(spec) || "AUTOINCREMENT".equals(spec) || "IDENTITY".equals(spec)) {
                    isAutoIncrement = true;
                } else if ("PRIMARY".equals(spec)) {
                    isPrimaryKey = true;
                } else if ("KEY".equals(spec) && j > 0 && "PRIMARY".equalsIgnoreCase(specs.get(j-1))) {
                    // 已处理
                } else if ("NOT".equals(spec)) {
                    isNotNull = true;
                } else if ("NULL".equals(spec) && j > 0 && "NOT".equalsIgnoreCase(specs.get(j-1))) {
                    // 已处理
                } else if ("UNIQUE".equals(spec)) {
                    isUnique = true;
                } else if ("DEFAULT".equals(spec) && j + 1 < specs.size()) {
                    defaultValStr = specs.get(j + 1);
                    j++;
                } else if ("COMMENT".equals(spec) && j + 1 < specs.size()) {
                    columnComment = specs.get(j + 1);
                    j++;
                } else if ("CHECK".equals(spec) && j + 1 < specs.size()) {
                    checkConstraint = "CONSTRAINT CHK_" + tableName + "_" + colName +
                            " CHECK (" + specs.get(j + 1) + ")";
                    j++;
                }
            }

            // 构建字段定义
            sqlServerSql.append("    ").append(colName).append(" ").append(colType);

            if (isAutoIncrement) {
                sqlServerSql.append(" IDENTITY(1,1)");
            }

            if (defaultValStr != null) {
                defaultValStr = defaultValStr.trim();
                if (defaultValStr.contains("CURRENT_TIMESTAMP") ||
                        defaultValStr.contains("NOW()") ||
                        defaultValStr.contains("CURRENT_DATE")) {
                    sqlServerSql.append(" DEFAULT GETDATE()");
                } else if (colType.equalsIgnoreCase("BIT") &&
                        (defaultValStr.equalsIgnoreCase("true") ||
                                defaultValStr.equalsIgnoreCase("false"))) {
                    sqlServerSql.append(" DEFAULT ").append(defaultValStr.equalsIgnoreCase("true") ? "1" : "0");
                } else if (defaultValStr.startsWith("'") && defaultValStr.endsWith("'")) {
                    sqlServerSql.append(" DEFAULT ").append(defaultValStr);
                } else {
                    sqlServerSql.append(" DEFAULT ").append(defaultValStr);
                }
            } else if (colType.equalsIgnoreCase("BIT")) {
                sqlServerSql.append(" DEFAULT 0");
            }

            if (isNotNull) {
                sqlServerSql.append(" NOT NULL");
            } else {
                sqlServerSql.append(" NULL");
            }

            if (isPrimaryKey) {
                String pkConstraint = "CONSTRAINT PK_" + tableName + " PRIMARY KEY (" + colName + ")";
                tableConstraints.get(tableName).add(pkConstraint);
            } else if (isUnique) {
                String ukConstraint = "CONSTRAINT UK_" + tableName + "_" + colName + " UNIQUE (" + colName + ")";
                tableConstraints.get(tableName).add(ukConstraint);
            }

            if (checkConstraint != null) {
                tableConstraints.get(tableName).add(checkConstraint);
            }

            // 处理字段注释
            if (columnComment != null && !columnComment.isEmpty()) {
                columnComment = columnComment.replaceAll("^['\"]|['\"]$", "");
                comments.add("EXEC sp_addextendedproperty \n" +
                        "    @name = N'MS_Description', \n" +
                        "    @value = N'" + columnComment.replace("'", "''") + "', \n" +
                        "    @level0type = N'SCHEMA', @level0name = N'dbo', \n" +
                        "    @level1type = N'TABLE', @level1name = N'" + tableName.replace("[", "").replace("]", "") + "', \n" +
                        "    @level2type = N'COLUMN', @level2name = N'" + colName.replace("[", "").replace("]", "") + "';\n");
            }
        }

        // 添加表级约束
        List<String> constraints = tableConstraints.get(tableName);
        if (!constraints.isEmpty()) {
            sqlServerSql.append(",\n");
            for (int i = 0; i < constraints.size(); i++) {
                sqlServerSql.append("    ").append(constraints.get(i));
                if (i < constraints.size() - 1) {
                    sqlServerSql.append(",\n");
                }
            }
        }

        sqlServerSql.append("\n);\nGO\n\n");

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
            comments.add(0, "EXEC sp_addextendedproperty \n" +
                    "    @name = N'MS_Description', \n" +
                    "    @value = N'" + tableComment + "', \n" +
                    "    @level0type = N'SCHEMA', @level0name = N'dbo', \n" +
                    "    @level1type = N'TABLE', @level1name = N'" + tableName.replace("[", "").replace("]", "") + "';\nGO\n\n");
        }

        // 添加所有comment语句
        if (!comments.isEmpty()) {
            for (String cmt : comments) {
                sqlServerSql.append(cmt);
            }
            comments.clear();
        }
        tableConstraints.remove(tableName);
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

        sqlServerSql.append("CREATE");
        if (isUnique) sqlServerSql.append(" UNIQUE");
        sqlServerSql.append(" INDEX ").append(indexName)
                .append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(");\nGO\n\n");
    }

    // 处理 INSERT
    @Override
    public void visit(Insert insert) {
        String tableName = cleanIdentifier(insert.getTable().getName());
        sqlServerSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            sqlServerSql.append(" (");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                sqlServerSql.append(colName);
                if (i < columns.size() - 1) sqlServerSql.append(", ");
            }
            sqlServerSql.append(")");
        }

        String valuesStr = insert.toString().toUpperCase();
        int valuesIdx = valuesStr.indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = insert.toString().substring(valuesIdx + 6);
            valuesPart = valuesPart.replace("CURRENT_TIMESTAMP", "GETDATE()");
            valuesPart = valuesPart.replace("NOW()", "GETDATE()");
            valuesPart = replaceBooleanLiterals(valuesPart);
        }

        sqlServerSql.append(" VALUES").append(valuesPart).append(";\nGO\n\n");
    }

    // 处理 UPDATE
    @Override
    public void visit(Update update) {
        String tableName = cleanIdentifier(update.getTable().getName());
        sqlServerSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = valueExpr.replace("CURRENT_TIMESTAMP", "GETDATE()");
            valueExpr = valueExpr.replace("NOW()", "GETDATE()");
            valueExpr = replaceBooleanLiterals(valueExpr);
            valueExpr = uppercaseWhereColumnNames(valueExpr);
            sqlServerSql.append(colName).append(" = ").append(valueExpr);
            if (i < cols.size() - 1) sqlServerSql.append(", ");
        }

        sqlServerSql.append(processWhereExpression(update.getWhere())).append(";\nGO\n\n");
    }

    // 处理 DELETE
    @Override
    public void visit(Delete delete) {
        String tableName = cleanIdentifier(delete.getTable().getName());
        sqlServerSql.append("DELETE FROM ").append(tableName);
        sqlServerSql.append(processWhereExpression(delete.getWhere())).append(";\nGO\n\n");
    }

    // 获取最终 SQL Server SQL
    public String getSqlServerSql() {
        return sqlServerSql.toString();
    }
}