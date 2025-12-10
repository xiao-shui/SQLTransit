package org.example.SqlTransit.tool;

import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.Function;
import net.sf.jsqlparser.expression.StringValue;
import net.sf.jsqlparser.expression.DoubleValue;
import net.sf.jsqlparser.expression.DateValue;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.operators.relational.ExpressionList;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.statement.comment.Comment;
import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.update.Update;

import java.lang.reflect.Method;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PostgresqlToMysqlVisitor extends StatementVisitorAdapter {
    private final StringBuilder mysqlSql = new StringBuilder();

    // 收集所有信息，最后统一输出
    private static class TableInfo {
        String tableName;
        List<ColumnInfo> columns = new ArrayList<>();
        List<String> primaryKeys = new ArrayList<>();
        List<String> uniqueKeys = new ArrayList<>();
        String tableComment;
        boolean hasTableDefinition = false;
    }

    private static class ColumnInfo {
        String name;
        String type;
        boolean isPrimaryKey;
        boolean isUnique;
        boolean isNotNull;
        boolean isAutoIncrement;
        String defaultValue;
        String checkConstraint;
        String columnComment;
    }

    private final Map<String, TableInfo> tables = new LinkedHashMap<>();
    private final List<String> otherStatements = new ArrayList<>(); // INSERT, UPDATE, DELETE等

    /**
     * 强制清洗标识符为小写（彻底移除引号，转为小写）
     */
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        // 移除所有引号/反引号，强制转小写
        return name.replaceAll("^[\"`']+|[\"`']+$", "").toLowerCase(Locale.ROOT).trim();
    }

    private String convertDataType(String postgresqlType, List<String> args) {
        if (postgresqlType == null) return "VARCHAR(255)";
        String type = postgresqlType.toUpperCase(Locale.ROOT);

        switch (type) {
            case "INTEGER":
            case "INT":
                return "INT";
            case "SMALLINT":
                return "SMALLINT";
            case "BIGINT":
                return "BIGINT";
            case "SERIAL":
                return "INT AUTO_INCREMENT";
            case "BIGSERIAL":
                return "BIGINT AUTO_INCREMENT";
            case "VARCHAR":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR(" + args.get(0) + ")";
                }
                return "VARCHAR(255)";
            case "CHAR":
            case "CHARACTER":
                if (args != null && !args.isEmpty()) {
                    return "CHAR(" + args.get(0) + ")";
                }
                return "CHAR(1)";
            case "TEXT":
                return "TEXT";
            case "BYTEA":
                return "LONGBLOB";
            case "BOOLEAN":
                return "BOOLEAN";
            case "REAL":
                return "FLOAT";
            case "DOUBLE PRECISION":
            case "FLOAT8":
                return "DOUBLE";
            case "NUMERIC":
            case "DECIMAL":
                if (args != null && args.size() == 2) {
                    return "DECIMAL(" + args.get(0) + "," + args.get(1) + ")";
                } else if (args != null && !args.isEmpty()) {
                    return "DECIMAL(" + args.get(0) + ")";
                }
                return "DECIMAL(10,2)";
            case "DATE":
                return "DATE";
            case "TIMESTAMP":
            case "TIMESTAMP WITHOUT TIME ZONE":
                return "DATETIME";
            case "TIMESTAMPTZ":
            case "TIMESTAMP WITH TIME ZONE":
                return "DATETIME";
            case "TIME":
                return "TIME";
            case "INTERVAL":
                return "VARCHAR(100)";
            case "MONEY":
                return "DECIMAL(15,2)";
            case "JSON":
            case "JSONB":
                return "JSON";
            case "UUID":
                return "VARCHAR(36)";
            case "CIDR":
            case "INET":
            case "MACADDR":
                return "VARCHAR(45)";
            case "BIT":
            case "BIT VARYING":
                return "VARBINARY";
            case "ARRAY":
                return "TEXT"; // MySQL不支持数组，转为TEXT
            case "XML":
                return "LONGTEXT";
            case "TSVECTOR":
            case "TSQUERY":
                return "TEXT";
            case "POINT":
            case "LINE":
            case "LSEG":
            case "BOX":
            case "PATH":
            case "POLYGON":
            case "CIRCLE":
                return "GEOMETRY"; // PostgreSQL几何类型转MySQL的GEOMETRY
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + String.join(",", args) + ")";
                }
                return type;
        }
    }

    @Override
    public void visit(CreateTable createTable) {
        // 强制表名小写
        String tableName = cleanIdentifier(createTable.getTable().getName());
        TableInfo tableInfo = tables.computeIfAbsent(tableName, k -> new TableInfo());
        tableInfo.tableName = tableName;
        tableInfo.hasTableDefinition = true;
        tableInfo.primaryKeys.clear();
        tableInfo.uniqueKeys.clear();

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();
        if (columns == null) {
            return;
        }

        for (ColumnDefinition col : columns) {
            ColumnInfo colInfo = new ColumnInfo();
            // 强制字段名小写
            colInfo.name = cleanIdentifier(col.getColumnName());
            colInfo.type = convertDataType(
                    col.getColDataType().getDataType(),
                    col.getColDataType().getArgumentsStringList()
            );

            List<String> columnSpecs = getColumnSpecs(col);

            // 处理列约束
            for (int j = 0; j < columnSpecs.size(); j++) {
                String spec = columnSpecs.get(j);
                if (spec == null) continue;

                String specUpper = spec.toUpperCase(Locale.ROOT);

                // 检查双词组合
                if (j + 1 < columnSpecs.size()) {
                    String nextSpec = columnSpecs.get(j + 1);
                    String twoWords = specUpper + " " + (nextSpec != null ? nextSpec.toUpperCase(Locale.ROOT) : "");

                    if ("PRIMARY KEY".equals(twoWords)) {
                        colInfo.isPrimaryKey = true;
                        tableInfo.primaryKeys.add(colInfo.name);
                        j++;
                        continue;
                    }
                    if ("NOT NULL".equals(twoWords)) {
                        colInfo.isNotNull = true;
                        j++;
                        continue;
                    }
                    if ("FOREIGN KEY".equals(twoWords)) {
                        j++; // 跳过KEY
                        continue;
                    }
                }

                // 处理PostgreSQL特有的约束
                switch (specUpper) {
                    case "PRIMARY":
                        colInfo.isPrimaryKey = true;
                        tableInfo.primaryKeys.add(colInfo.name);
                        break;
                    case "UNIQUE":
                        colInfo.isUnique = true;
                        tableInfo.uniqueKeys.add(colInfo.name);
                        break;
                    case "NOT":
                        colInfo.isNotNull = true;
                        break;
                    case "DEFAULT":
                        if (j + 1 < columnSpecs.size()) {
                            colInfo.defaultValue = columnSpecs.get(j + 1);
                            j++;
                        }
                        break;
                    case "CHECK":
                        if (j + 1 < columnSpecs.size()) {
                            colInfo.checkConstraint = columnSpecs.get(j + 1);
                            j++;
                        }
                        break;
                    case "AUTO_INCREMENT":
                    case "IDENTITY":
                    case "GENERATED":
                        if (j + 2 < columnSpecs.size()
                                && "BY".equalsIgnoreCase(columnSpecs.get(j + 1))
                                && "DEFAULT".equalsIgnoreCase(columnSpecs.get(j + 2))) {
                            colInfo.isAutoIncrement = true;
                            j += 2;
                        } else if ("ALWAYS".equalsIgnoreCase(specUpper) && j > 0
                                && "GENERATED".equalsIgnoreCase(columnSpecs.get(j-1).toUpperCase(Locale.ROOT))) {
                            colInfo.isAutoIncrement = true;
                        }
                        break;
                    case "REFERENCES":
                        // 外键约束，跳过参数
                        while (j + 1 < columnSpecs.size() && !columnSpecs.get(j + 1).toUpperCase(Locale.ROOT)
                                .matches("^(PRIMARY|UNIQUE|NOT|DEFAULT|CHECK|COMMENT)$")) {
                            j++;
                        }
                        break;
                }
            }

            // 处理默认值转换
            if (colInfo.defaultValue != null) {
                String defaultValue = colInfo.defaultValue.toUpperCase(Locale.ROOT);
                if (defaultValue.contains("CURRENT_TIMESTAMP") ||
                        defaultValue.contains("NOW()") ||
                        defaultValue.contains("CURRENT_DATE") ||
                        defaultValue.contains("CURRENT_TIME")) {
                    colInfo.defaultValue = "CURRENT_TIMESTAMP";
                } else if (defaultValue.contains("TRUE") || defaultValue.contains("'T'") || defaultValue.contains("'t'")) {
                    colInfo.defaultValue = "TRUE";
                } else if (defaultValue.contains("FALSE") || defaultValue.contains("'F'") || defaultValue.contains("'f'")) {
                    colInfo.defaultValue = "FALSE";
                } else if (defaultValue.contains("NULL")) {
                    colInfo.defaultValue = "NULL";
                }
                // 移除PostgreSQL的类型转换::type
                colInfo.defaultValue = colInfo.defaultValue.replaceAll("::\\w+", "");
            }

            // 字段注释合并：如果在tableInfo已有注释（来自COMMENT ON COLUMN），则优先该注释
            if (tableInfo.columns != null) {
                for (ColumnInfo existCol : tableInfo.columns) {
                    if (existCol.name.equals(colInfo.name) && existCol.columnComment != null) {
                        colInfo.columnComment = existCol.columnComment;
                        break;
                    }
                }
            }
            tableInfo.columns.add(colInfo);
        }
    }

    @Override
    public void visit(Comment comment) {
        // PostgreSQL注释语法：COMMENT ON TABLE table_name IS 'comment'
        // 或：COMMENT ON COLUMN table_name.column_name IS 'comment'
        String commentText = null;
        if (comment.getComment() instanceof StringValue) {
            StringValue stringValue = (StringValue) comment.getComment();
            commentText = stringValue.getValue().trim();
        } else if (comment.getComment() != null) {
            commentText = cleanCommentValue(comment.getComment().toString());
        }
        // 注释内容可以是空字符串，不能就跳过——MySQL允许空的COMMENT
        if (commentText == null) {
            commentText = "";
        }

        // 处理表注释/字段注释
        if (comment.getTable() != null) {
            String tableName = cleanIdentifier(comment.getTable().getName());
            TableInfo tableInfo = tables.computeIfAbsent(tableName, k -> new TableInfo());
            tableInfo.tableName = tableName;

            if (comment.getColumn() != null) {
                // 字段注释：强制字段名小写
                String columnName = cleanIdentifier(comment.getColumn().getColumnName());
                // 确保列存在（兼容先注释后建表、也兼容先建表后注释的场景）
                ColumnInfo colInfo = tableInfo.columns.stream()
                        .filter(c -> c.name.equals(columnName))
                        .findFirst()
                        .orElseGet(() -> {
                            ColumnInfo newCol = new ColumnInfo();
                            newCol.name = columnName;
                            newCol.type = "VARCHAR(255)";
                            tableInfo.columns.add(newCol);
                            return newCol;
                        });
                // 保存注释
                colInfo.columnComment = commentText;
            } else {
                tableInfo.tableComment = commentText;
            }
        }
    }

    @Override
    public void visit(Insert insert) {
        // 收集INSERT语句，最后统一输出
        otherStatements.add(convertInsert(insert));
    }

    @Override
    public void visit(Update update) {
        // 收集UPDATE语句，最后统一输出
        otherStatements.add(convertUpdate(update));
    }

    @Override
    public void visit(Delete delete) {
        // 收集DELETE语句，最后统一输出
        otherStatements.add(convertDelete(delete));
    }

    private void generateTableDefinitions() {
        // 生成所有表的定义
        for (TableInfo tableInfo : tables.values()) {
            if (!tableInfo.hasTableDefinition) {
                continue; // 如果没有表定义，只有注释，不生成CREATE TABLE
            }

            mysqlSql.append("CREATE TABLE IF NOT EXISTS ").append(tableInfo.tableName).append(" (\n");

            for (int i = 0; i < tableInfo.columns.size(); i++) {
                ColumnInfo col = tableInfo.columns.get(i);
                if (i > 0) mysqlSql.append(",\n");

                mysqlSql.append("    ").append(col.name).append(" ").append(col.type);

                if (col.defaultValue != null) {
                    mysqlSql.append(" DEFAULT ").append(col.defaultValue);
                }

                if (col.isAutoIncrement) {
                    mysqlSql.append(" AUTO_INCREMENT");
                }

                if (col.isPrimaryKey) {
                    mysqlSql.append(" PRIMARY KEY");
                }

                if (col.isNotNull) {
                    mysqlSql.append(" NOT NULL");
                }

                if (col.isUnique) {
                    mysqlSql.append(" UNIQUE");
                }

                if (col.checkConstraint != null && !col.checkConstraint.isEmpty()) {
                    // 转换PostgreSQL的CHECK约束语法
                    String checkConstraint = col.checkConstraint;
                    checkConstraint = checkConstraint.replaceAll("(?i)\\bTRUE\\b", "1");
                    checkConstraint = checkConstraint.replaceAll("(?i)\\bFALSE\\b", "0");
                    mysqlSql.append(" CHECK ").append(checkConstraint);
                }

                // 始终加 COMMENT 子句（哪怕是空字符串）
                if (col.columnComment != null) {
                    mysqlSql.append(" COMMENT '").append(escapeComment(col.columnComment)).append("'");
                }
            }

            // 表级约束
            boolean hasTableConstraint = false;

            // 主键约束
            if (!tableInfo.primaryKeys.isEmpty()) {
                mysqlSql.append(",\n    PRIMARY KEY (");
                for (int i = 0; i < tableInfo.primaryKeys.size(); i++) {
                    if (i > 0) mysqlSql.append(", ");
                    mysqlSql.append(tableInfo.primaryKeys.get(i));
                }
                mysqlSql.append(")");
                hasTableConstraint = true;
            }

            // 唯一约束
            if (!tableInfo.uniqueKeys.isEmpty()) {
                mysqlSql.append(",\n    UNIQUE (");
                for (int i = 0; i < tableInfo.uniqueKeys.size(); i++) {
                    if (i > 0) mysqlSql.append(", ");
                    mysqlSql.append(tableInfo.uniqueKeys.get(i));
                }
                mysqlSql.append(")");
                hasTableConstraint = true;
            }

            mysqlSql.append("\n)");

            // 添加表注释
            if (tableInfo.tableComment != null) {
                mysqlSql.append(" COMMENT='").append(escapeComment(tableInfo.tableComment)).append("'");
            }

            mysqlSql.append(";\n\n");
        }

        // 输出其他语句（INSERT, UPDATE, DELETE）
        for (String stmt : otherStatements) {
            mysqlSql.append(stmt);
        }
    }

    private String convertInsert(Insert insert) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(insert.getTable().getName());
        sb.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            sb.append(" (");
            for (int i = 0; i < columns.size(); i++) {
                sb.append(cleanIdentifier(columns.get(i).getColumnName()));
                if (i < columns.size() - 1) {
                    sb.append(", ");
                }
            }
            sb.append(")");
        }

        try {
            Method getValuesMethod = Insert.class.getMethod("getValues");
            Object values = getValuesMethod.invoke(insert);

            if (values instanceof ExpressionList) {
                ExpressionList exprList = (ExpressionList) values;
                @SuppressWarnings("unchecked")
                List<Expression> expressions = (List<Expression>) (List<?>) exprList.getExpressions();
                sb.append(" VALUES (");
                for (int i = 0; i < expressions.size(); i++) {
                    Expression expr = expressions.get(i);
                    sb.append(convertExpression(expr));
                    if (i < expressions.size() - 1) {
                        sb.append(", ");
                    }
                }
                sb.append(")");
            } else if (values != null) {
                sb.append(" ").append(values.toString());
            }
        } catch (Exception e) {
            sb.append("/* 解析INSERT出错 */");
        }

        return sb.append(";\n\n").toString();
    }

    private String convertUpdate(Update update) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(update.getTable().getName());
        sb.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> columns = update.getColumns();
        @SuppressWarnings("unchecked")
        List<Expression> expressions = (List<Expression>) (List<?>) update.getExpressions();

        for (int i = 0; i < columns.size(); i++) {
            Column column = columns.get(i);
            Expression expression = expressions.get(i);
            sb.append(cleanIdentifier(column.getColumnName()))
                    .append(" = ");
            sb.append(convertExpression(expression));
            if (i < columns.size() - 1) {
                sb.append(", ");
            }
        }

        Expression where = update.getWhere();
        if (where != null) {
            sb.append(" WHERE ").append(convertExpression(where));
        }

        return sb.append(";\n\n").toString();
    }

    private String convertDelete(Delete delete) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(delete.getTable().getName());
        sb.append("DELETE FROM ").append(tableName);

        Expression where = delete.getWhere();
        if (where != null) {
            sb.append(" WHERE ").append(convertExpression(where));
        }

        return sb.append(";\n\n").toString();
    }

    private String convertExpression(Expression expression) {
        if (expression == null) return "";

        if (expression instanceof StringValue) {
            StringValue strVal = (StringValue) expression;
            return "'" + strVal.getValue().replace("'", "''") + "'";
        }
        if (expression instanceof LongValue) {
            LongValue longVal = (LongValue) expression;
            return String.valueOf(longVal.getValue());
        }
        if (expression instanceof DoubleValue) {
            DoubleValue doubleVal = (DoubleValue) expression;
            return String.valueOf(doubleVal.getValue());
        }
        if (expression instanceof DateValue) {
            DateValue dateVal = (DateValue) expression;
            return "'" + dateVal.getValue() + "'";
        }
        if (expression instanceof Function) {
            Function function = (Function) expression;
            String functionName = function.getName();
            List<Expression> params = new ArrayList<>();

            ExpressionList exprList = function.getParameters();
            if (exprList != null) {
                params = exprList.getExpressions();
            }

            // PostgreSQL函数转MySQL函数
            switch (functionName.toUpperCase(Locale.ROOT)) {
                case "CURRENT_TIMESTAMP":
                case "NOW":
                case "LOCALTIMESTAMP":
                    return "NOW()";
                case "CURRENT_DATE":
                case "LOCALDATE":
                    return "CURDATE()";
                case "CURRENT_TIME":
                case "LOCALTIME":
                    return "CURTIME()";
                case "COALESCE":
                    if (params != null && !params.isEmpty()) {
                        StringBuilder sb = new StringBuilder("COALESCE(");
                        for (int i = 0; i < params.size(); i++) {
                            if (i > 0) sb.append(", ");
                            sb.append(convertExpression(params.get(i)));
                        }
                        sb.append(")");
                        return sb.toString();
                    }
                    break;
                case "SUBSTRING":
                    if (params != null && params.size() >= 2) {
                        String str = convertExpression(params.get(0));
                        String start = convertExpression(params.get(1));
                        if (params.size() >= 3) {
                            String length = convertExpression(params.get(2));
                            return "SUBSTRING(" + str + ", " + start + ", " + length + ")";
                        }
                        return "SUBSTRING(" + str + ", " + start + ")";
                    }
                    break;
                case "TO_CHAR":
                    if (params != null && params.size() >= 1) {
                        String expr = convertExpression(params.get(0));
                        // 简化处理：转换为字符串
                        return "CAST(" + expr + " AS CHAR)";
                    }
                    break;
                case "TO_DATE":
                    if (params != null && params.size() >= 2) {
                        String dateStr = convertExpression(params.get(0));
                        String format = params.get(1).toString().replaceAll("['\"]", "");
                        String mysqlFormat = convertDateFormat(format);
                        return "STR_TO_DATE(" + dateStr + ", " + mysqlFormat + ")";
                    }
                    break;
                case "TO_TIMESTAMP":
                    if (params != null && params.size() >= 2) {
                        String dateStr = convertExpression(params.get(0));
                        String format = params.get(1).toString().replaceAll("['\"]", "");
                        String mysqlFormat = convertDateFormat(format);
                        return "STR_TO_DATE(" + dateStr + ", " + mysqlFormat + ")";
                    } else if (params != null && !params.isEmpty()) {
                        // 转换UNIX时间戳
                        return "FROM_UNIXTIME(" + convertExpression(params.get(0)) + ")";
                    }
                    break;
                case "CONCAT":
                case "CONCAT_WS":
                    if (params != null && !params.isEmpty()) {
                        StringBuilder sb = new StringBuilder("CONCAT(");
                        for (int i = 0; i < params.size(); i++) {
                            if (i > 0) sb.append(", ");
                            sb.append(convertExpression(params.get(i)));
                        }
                        sb.append(")");
                        return sb.toString();
                    }
                    break;
                case "STRING_AGG":
                    if (params != null && params.size() >= 1) {
                        String expr = convertExpression(params.get(0));
                        String delimiter = params.size() >= 2 ? convertExpression(params.get(1)) : "','";
                        return "GROUP_CONCAT(" + expr + " SEPARATOR " + delimiter + ")";
                    }
                    break;
                case "EXTRACT":
                    if (params != null && params.size() >= 1) {
                        String extractField = params.get(0).toString().toUpperCase(Locale.ROOT);
                        String source = params.size() >= 2 ? convertExpression(params.get(1)) : "";
                        switch (extractField) {
                            case "EPOCH":
                                return "UNIX_TIMESTAMP(" + source + ")";
                            case "YEAR":
                                return "YEAR(" + source + ")";
                            case "MONTH":
                                return "MONTH(" + source + ")";
                            case "DAY":
                                return "DAY(" + source + ")";
                            case "HOUR":
                                return "HOUR(" + source + ")";
                            case "MINUTE":
                                return "MINUTE(" + source + ")";
                            case "SECOND":
                                return "SECOND(" + source + ")";
                            default:
                                return "EXTRACT(" + extractField + " FROM " + source + ")";
                        }
                    }
                    break;
            }

            // 其他函数：保持原样但转换参数
            StringBuilder funcCall = new StringBuilder(functionName).append("(");
            if (params != null) {
                for (int i = 0; i < params.size(); i++) {
                    if (i > 0) funcCall.append(", ");
                    funcCall.append(convertExpression(params.get(i)));
                }
            }
            funcCall.append(")");
            return funcCall.toString();
        }
        if (expression instanceof Column) {
            Column column = (Column) expression;
            return cleanIdentifier(column.getColumnName());
        }

        // 处理其他表达式类型...
        String exprStr = expression.toString();
        // 转换PostgreSQL的布尔字面量
        exprStr = exprStr.replaceAll("(?i)\\bTRUE\\b", "1");
        exprStr = exprStr.replaceAll("(?i)\\bFALSE\\b", "0");
        // 转换PostgreSQL的类型转换语法 ::type
        exprStr = exprStr.replaceAll("::\\w+", "");
        return exprStr;
    }

    private String convertDateFormat(String postgresqlFormat) {
        String format = postgresqlFormat.toUpperCase(Locale.ROOT);
        Map<String, String> formatMap = new HashMap<>();
        formatMap.put("YYYY", "%Y");
        formatMap.put("YY", "%y");
        formatMap.put("MM", "%m");
        formatMap.put("DD", "%d");
        formatMap.put("HH24", "%H");
        formatMap.put("HH12", "%h");
        formatMap.put("HH", "%h");
        formatMap.put("MI", "%i");
        formatMap.put("SS", "%s");
        formatMap.put("DAY", "%W");
        formatMap.put("DY", "%a");
        formatMap.put("MON", "%b");
        formatMap.put("MONTH", "%M");
        formatMap.put("YEAR", "%Y");

        for (Map.Entry<String, String> entry : formatMap.entrySet()) {
            format = format.replace(entry.getKey(), entry.getValue());
        }

        return "'" + format + "'";
    }

    private List<String> getColumnSpecs(ColumnDefinition col) {
        List<String> specs = new ArrayList<>();
        try {
            Method method = ColumnDefinition.class.getMethod("getColumnSpecs");
            @SuppressWarnings("unchecked")
            List<String> columnSpecs = (List<String>) method.invoke(col);
            if (columnSpecs != null) {
                specs.addAll(columnSpecs);
            }
        } catch (Exception e) {
            String colStr = col.toString();
            int typeEnd = colStr.indexOf(" ", col.getColumnName().length() + 1);
            if (typeEnd > 0) {
                String constraintPart = colStr.substring(typeEnd).trim();
                Pattern pattern = Pattern.compile("([^\\s'\"]+|\"[^\"]*\"|'[^']*')");
                Matcher matcher = pattern.matcher(constraintPart);
                while (matcher.find()) {
                    specs.add(matcher.group());
                }
            }
        }
        return specs;
    }

    private String cleanCommentValue(String val) {
        if (val == null) return "";
        // 移除注释前后的引号，保留内容
        return val.replaceAll("^['\"]+|['\"]+$", "").trim();
    }

    private String escapeComment(String comment) {
        if (comment == null) return "";
        // 转义单引号和反斜杠，避免SQL语法错误
        return comment.replace("'", "''").replace("\\", "\\\\");
    }

    public String getMysqlSql() {
        // 在获取最终SQL时，生成所有表的定义
        if (mysqlSql.length() == 0) {
            generateTableDefinitions();
        }
        return mysqlSql.toString();
    }

    public void clear() {
        mysqlSql.setLength(0);
        tables.clear();
        otherStatements.clear();
    }
}