package org.example.SqlTransit.tool;

import net.sf.jsqlparser.expression.operators.relational.*;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.statement.comment.Comment;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.expression.operators.conditional.AndExpression;
import net.sf.jsqlparser.expression.operators.conditional.OrExpression;
import net.sf.jsqlparser.expression.*;
import net.sf.jsqlparser.statement.select.*;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class OracleToMysqlVisitor extends StatementVisitorAdapter {
    private final StringBuilder mysqlSql = new StringBuilder();
    private final List<String> comments = new ArrayList<>();
    private final List<String> primaryKeys = new ArrayList<>();
    private final List<String> uniqueKeys = new ArrayList<>();
    private final Map<String, String> columnComments = new HashMap<>();

    private String cleanIdentifier(String name) {
        if (name == null) return null;
        // 移除引号并转为小写
        return name.replaceAll("^[\"`']+|[\"`']+$", "").toLowerCase();
    }

    private String convertDataType(String oracleType, List<String> args) {
        if (oracleType == null) return "VARCHAR(255)";
        String type = oracleType.toUpperCase();
        switch (type) {
            case "NUMBER":
                if (args != null && args.size() == 2) {
                    return "DECIMAL(" + args.get(0) + "," + args.get(1) + ")";
                } else if (args != null && args.size() == 1) {
                    int precision = Integer.parseInt(args.get(0));
                    if (precision <= 10) {
                        return "INT";
                    } else if (precision <= 19) {
                        return "BIGINT";
                    } else {
                        return "DECIMAL(" + args.get(0) + ")";
                    }
                }
                return "DECIMAL(10,2)";
            case "VARCHAR2":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR(" + args.get(0) + ")";
                }
                return "VARCHAR(255)";
            case "NVARCHAR2":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR(" + args.get(0) + ") CHARACTER SET utf8mb4";
                }
                return "VARCHAR(255) CHARACTER SET utf8mb4";
            case "CHAR":
                if (args != null && !args.isEmpty()) {
                    return "CHAR(" + args.get(0) + ")";
                }
                return "CHAR(1)";
            case "NCHAR":
                if (args != null && !args.isEmpty()) {
                    return "CHAR(" + args.get(0) + ") CHARACTER SET utf8mb4";
                }
                return "CHAR(1) CHARACTER SET utf8mb4";
            case "DATE":
                return "DATETIME";
            case "TIMESTAMP":
                return "DATETIME";
            case "CLOB":
            case "NCLOB":
                return "LONGTEXT";
            case "BLOB":
                return "LONGBLOB";
            case "RAW":
                if (args != null && !args.isEmpty()) {
                    return "VARBINARY(" + args.get(0) + ")";
                }
                return "VARBINARY(255)";
            case "LONG":
                return "LONGTEXT";
            case "FLOAT":
                return "DOUBLE";
            case "BINARY_FLOAT":
                return "FLOAT";
            case "BINARY_DOUBLE":
                return "DOUBLE";
            case "INTERVAL":
                return "VARCHAR(50)";
            case "XMLTYPE":
                return "LONGTEXT";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + String.join(",", args) + ")";
                }
                return type;
        }
    }

    private String convertFunction(String functionName, List<Expression> params) {
        if (functionName == null) return "";
        String funcName = functionName.toUpperCase();
        switch (funcName) {
            case "TO_DATE":
                if (params != null && params.size() >= 1) {
                    String dateStr = params.get(0).toString();
                    String format = params.size() >= 2 ? convertDateFormat(params.get(1).toString()) : "'%Y-%m-%d'";
                    return "STR_TO_DATE(" + dateStr + ", " + format + ")";
                }
                break;
            case "TO_CHAR":
                if (params != null && !params.isEmpty()) {
                    String expr = params.get(0).toString();
                    String format = params.size() >= 2 ? convertDateFormat(params.get(1).toString()) : "'%Y-%m-%d %H:%i:%s'";
                    return "DATE_FORMAT(" + expr + ", " + format + ")";
                }
                break;
            case "TO_NUMBER":
                if (params != null && !params.isEmpty()) {
                    return "CAST(" + params.get(0).toString() + " AS DECIMAL)";
                }
                break;
            case "SYSDATE":
                return "NOW()";
            case "SYSTIMESTAMP":
                return "NOW()";
            case "NVL":
                if (params != null && params.size() == 2) {
                    return "IFNULL(" + params.get(0).toString() + ", " + params.get(1).toString() + ")";
                }
                break;
            case "NVL2":
                if (params != null && params.size() == 3) {
                    return "IF(" + params.get(0).toString() + " IS NOT NULL, " +
                            params.get(1).toString() + ", " + params.get(2).toString() + ")";
                }
                break;
            case "DECODE":
                if (params != null && params.size() >= 3) {
                    StringBuilder caseExpr = new StringBuilder("CASE ");
                    caseExpr.append(params.get(0).toString());
                    for (int i = 1; i < params.size(); i += 2) {
                        if (i + 1 < params.size()) {
                            caseExpr.append(" WHEN ").append(params.get(i).toString())
                                    .append(" THEN ").append(params.get(i + 1).toString());
                        } else {
                            caseExpr.append(" ELSE ").append(params.get(i).toString());
                        }
                    }
                    caseExpr.append(" END");
                    return caseExpr.toString();
                }
                break;
            case "ROWNUM":
                return "/* ROWNUM - 需要在查询外部使用LIMIT处理 */";
            case "SUBSTR":
                if (params != null && params.size() >= 2) {
                    return "SUBSTRING(" + params.get(0).toString() + ", " + params.get(1).toString() +
                            (params.size() >= 3 ? ", " + params.get(2).toString() : "") + ")";
                }
                break;
            case "INSTR":
                if (params != null && params.size() >= 2) {
                    return "INSTR(" + params.get(0).toString() + ", " + params.get(1).toString() + ")";
                }
                break;
            case "CONCAT":
                if (params != null) {
                    StringBuilder concatExpr = new StringBuilder("CONCAT(");
                    for (int i = 0; i < params.size(); i++) {
                        if (i > 0) concatExpr.append(", ");
                        concatExpr.append(params.get(i).toString());
                    }
                    concatExpr.append(")");
                    return concatExpr.toString();
                }
                break;
        }
        StringBuilder funcCall = new StringBuilder(funcName).append("(");
        if (params != null) {
            for (int i = 0; i < params.size(); i++) {
                if (i > 0) funcCall.append(", ");
                funcCall.append(params.get(i).toString());
            }
        }
        funcCall.append(")");
        return funcCall.toString();
    }

    private String convertDateFormat(String oracleFormat) {
        String format = oracleFormat.replaceAll("['\"]", "");
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

    @Override
    public void visit(CreateTable createTable) {
        String tableName = cleanIdentifier(createTable.getTable().getName());
        mysqlSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        primaryKeys.clear();
        uniqueKeys.clear();
        columnComments.clear();

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) mysqlSql.append(",\n");

            String colName = cleanIdentifier(col.getColumnName());
            String colType = convertDataType(
                    col.getColDataType().getDataType(),
                    col.getColDataType().getArgumentsStringList()
            );

            mysqlSql.append("    ").append(colName).append(" ").append(colType);

            List<String> columnSpecs = getColumnSpecs(col);

            boolean isPrimaryKey = false;
            boolean isUnique = false;
            boolean isNotNull = false;
            boolean isAutoIncrement = false;
            String defaultValue = null;
            String checkConstraint = null;
            String columnComment = null;

            // 处理列约束和注释
            for (int j = 0; j < columnSpecs.size(); j++) {
                String spec = columnSpecs.get(j);
                if (spec == null) continue;

                String specUpper = spec.toUpperCase();

                // 检查双词组合
                if (j + 1 < columnSpecs.size()) {
                    String nextSpec = columnSpecs.get(j + 1);
                    String twoWords = specUpper + " " + (nextSpec != null ? nextSpec.toUpperCase() : "");

                    if ("PRIMARY KEY".equals(twoWords)) {
                        isPrimaryKey = true;
                        primaryKeys.add(colName);
                        j++;
                        continue;
                    }
                    if ("NOT NULL".equals(twoWords)) {
                        isNotNull = true;
                        j++;
                        continue;
                    }
                    if ("FOREIGN KEY".equals(twoWords)) {
                        // 外键约束暂时跳过
                        j++;
                        continue;
                    }
                }

                // 处理单词约束
                switch (specUpper) {
                    case "PRIMARY":
                        isPrimaryKey = true;
                        primaryKeys.add(colName);
                        break;
                    case "KEY":
                        // 单独出现的KEY忽略
                        break;
                    case "UNIQUE":
                        isUnique = true;
                        uniqueKeys.add(colName);
                        break;
                    case "NOT":
                        isNotNull = true;
                        break;
                    case "NULL":
                        break;
                    case "DEFAULT":
                        if (j + 1 < columnSpecs.size()) {
                            defaultValue = columnSpecs.get(j + 1);
                            j++;
                        }
                        break;
                    case "CHECK":
                        if (j + 1 < columnSpecs.size()) {
                            checkConstraint = columnSpecs.get(j + 1);
                            j++;
                        }
                        break;
                    case "AUTO_INCREMENT":
                        isAutoIncrement = true;
                        break;
                    case "IDENTITY":
                        isAutoIncrement = true;
                        break;
                    case "GENERATED":
                        if (j + 2 < columnSpecs.size()
                                && "BY".equalsIgnoreCase(columnSpecs.get(j + 1))
                                && "DEFAULT".equalsIgnoreCase(columnSpecs.get(j + 2))) {
                            isAutoIncrement = true;
                            j += 2;
                        }
                        break;
                    case "COMMENT":
                        if (j + 1 < columnSpecs.size()) {
                            columnComment = cleanCommentValue(columnSpecs.get(j + 1));
                            columnComments.put(colName, columnComment);
                            j++;
                        }
                        break;
                    case "REFERENCES":
                        // 外键引用，跳过后续参数
                        while (j + 1 < columnSpecs.size() &&
                                !columnSpecs.get(j + 1).toUpperCase().matches("^(PRIMARY|UNIQUE|NOT|DEFAULT|CHECK|COMMENT)$")) {
                            j++;
                        }
                        break;
                }
            }

            // 添加默认值
            if (defaultValue != null) {
                if (defaultValue.toUpperCase().contains("SYSDATE") ||
                        defaultValue.toUpperCase().contains("CURRENT_TIMESTAMP")) {
                    mysqlSql.append(" DEFAULT CURRENT_TIMESTAMP");
                } else if (defaultValue.toUpperCase().contains("NULL")) {
                    mysqlSql.append(" DEFAULT NULL");
                } else {
                    mysqlSql.append(" DEFAULT ").append(defaultValue);
                }
            }

            // 添加自动递增
            if (isAutoIncrement) {
                mysqlSql.append(" AUTO_INCREMENT");
            }

            if(isPrimaryKey){
                mysqlSql.append(" PRIMARY KEY ");
            }

            // 添加非空约束
            if (isNotNull) {
                mysqlSql.append(" NOT NULL");
            }

            // 添加唯一约束
            if (isUnique) {
                mysqlSql.append(" UNIQUE");
            }

            // 添加检查约束
            if (checkConstraint != null && !checkConstraint.isEmpty()) {
                mysqlSql.append(" CHECK ").append(checkConstraint);
            }

            // 添加字段注释
            if (columnComment != null && !columnComment.isEmpty()) {
                mysqlSql.append(" COMMENT '").append(escapeComment(columnComment)).append("'");
            }
        }

        // 添加主键约束（如果在列级别未声明）
        if (!primaryKeys.isEmpty()) {
            mysqlSql.append(",\n    PRIMARY KEY (");
            for (int i = 0; i < primaryKeys.size(); i++) {
                if (i > 0) mysqlSql.append(", ");
                mysqlSql.append(primaryKeys.get(i));
            }
            mysqlSql.append(")");
        }

        mysqlSql.append("\n)");

        // 添加表注释
        String tableComment = extractTableComment(createTable);
        if (tableComment != null && !tableComment.isEmpty()) {
            mysqlSql.append(" COMMENT='").append(escapeComment(tableComment)).append("'");
        }

        mysqlSql.append(";\n\n");
    }

    private String cleanCommentValue(String val) {
        if (val == null) return "";
        // 去除前后单引号或双引号
        return val.replaceAll("^['\"]+|['\"]+$", "").trim();
    }

    private List<String> getColumnSpecs(ColumnDefinition col) {
        List<String> specs = new ArrayList<>();
        try {
            java.lang.reflect.Method method = ColumnDefinition.class.getMethod("getColumnSpecs");
            @SuppressWarnings("unchecked")
            List<String> columnSpecs = (List<String>) method.invoke(col);
            if (columnSpecs != null) {
                specs.addAll(columnSpecs);
            }
        } catch (Exception e) {
            // 备选方案：解析字符串
            String colStr = col.toString();
            int typeEnd = colStr.indexOf(" ", col.getColumnName().length() + 1);
            if (typeEnd > 0) {
                String constraintPart = colStr.substring(typeEnd).trim();
                // 使用正则表达式更好地分割，保留引号内的内容
                Pattern pattern = Pattern.compile("([^\\s'\"]+|\"[^\"]*\"|'[^']*')");
                Matcher matcher = pattern.matcher(constraintPart);
                while (matcher.find()) {
                    specs.add(matcher.group());
                }
            }
        }
        return specs;
    }

    private String extractTableComment(CreateTable createTable) {
        try {
            java.lang.reflect.Method getOptionsMethod = CreateTable.class.getMethod("getTableOptionsStrings");
            @SuppressWarnings("unchecked")
            List<String> options = (List<String>) getOptionsMethod.invoke(createTable);
            if (options != null) {
                for (int i = 0; i < options.size(); i++) {
                    if ("COMMENT".equalsIgnoreCase(options.get(i).trim())) {
                        if (i + 1 < options.size()) {
                            return options.get(i + 1).replaceAll("^['\"]+|['\"]+$", "").trim();
                        }
                    }
                }
            }
        } catch (Exception e) {
            // 忽略异常，尝试其他方法
        }

        // 备选方案：从字符串中提取注释
        String createStr = createTable.toString();
        Pattern pattern = Pattern.compile("COMMENT\\s*=\\s*['\"]([^'\"]+)['\"]", Pattern.CASE_INSENSITIVE);
        Matcher matcher = pattern.matcher(createStr);
        if (matcher.find()) {
            return matcher.group(1).trim();
        }
        return null;
    }

    private String escapeComment(String comment) {
        if (comment == null) return "";
        return comment.replace("'", "''").replace("\\", "\\\\");
    }

    @Override
    public void visit(Insert insert) {
        String tableName = cleanIdentifier(insert.getTable().getName());
        mysqlSql.append("INSERT INTO ").append(tableName);

        // 处理列名
        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            mysqlSql.append(" (");
            for (int i = 0; i < columns.size(); i++) {
                mysqlSql.append(cleanIdentifier(columns.get(i).getColumnName()));
                if (i < columns.size() - 1) {
                    mysqlSql.append(", ");
                }
            }
            mysqlSql.append(")");
        }

        try {
            // 使用反射调用getValues()方法
            java.lang.reflect.Method getValuesMethod = Insert.class.getMethod("getValues");
            Object values = getValuesMethod.invoke(insert);

            if (values instanceof ExpressionList) {
                ExpressionList exprList = (ExpressionList) values;
                @SuppressWarnings("unchecked")
                List<Expression> expressions = (List<Expression>) (List<?>) exprList.getExpressions();

                for (int i = 0; i < expressions.size(); i++) {
                    Expression expr = expressions.get(i);
                    mysqlSql.append(convertExpression(expr));
                    if (i < expressions.size() - 1) {
                        mysqlSql.append(", ");
                    }
                }
            } else if (values != null) {
                // 如果getValues()返回的是其他类型，尝试toString
                mysqlSql.append(values.toString());
            }
        } catch (NoSuchMethodException e) {
            // 如果没有getValues()方法，尝试其他方法
            try {
                // 尝试getItemsList()方法（新版本可能叫这个）
                java.lang.reflect.Method getItemsListMethod = Insert.class.getMethod("getItemsList");
                Object itemsList = getItemsListMethod.invoke(insert);

                if (itemsList instanceof ExpressionList) {
                    ExpressionList exprList = (ExpressionList) itemsList;
                    @SuppressWarnings("unchecked")
                    List<Expression> expressions = (List<Expression>) (List<?>) exprList.getExpressions();

                    for (int i = 0; i < expressions.size(); i++) {
                        Expression expr = expressions.get(i);
                        mysqlSql.append(convertExpression(expr));
                        if (i < expressions.size() - 1) {
                            mysqlSql.append(", ");
                        }
                    }
                } else if (itemsList != null) {
                    mysqlSql.append(itemsList.toString());
                }
            } catch (Exception ex) {
                // 如果两个方法都没有，尝试使用toString解析
                String insertStr = insert.toString();
                Pattern pattern = Pattern.compile("VALUES\\s*\\((.+?)\\)", Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                Matcher matcher = pattern.matcher(insertStr);
                if (matcher.find()) {
                    mysqlSql.append(matcher.group(1));
                } else {
                    mysqlSql.append("/* 无法解析VALUES值 */");
                }
            }
        } catch (Exception e) {
            mysqlSql.append("/* 解析VALUES出错: ").append(e.getMessage()).append(" */");
        }

        mysqlSql.append(";\n\n");
    }

    @Override
    public void visit(Update update) {
        String tableName = cleanIdentifier(update.getTable().getName());
        mysqlSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> columns = update.getColumns();
        @SuppressWarnings("unchecked")
        List<Expression> expressions = (List<Expression>) (List<?>) update.getExpressions();

        for (int i = 0; i < columns.size(); i++) {
            Column column = columns.get(i);
            Expression expression = expressions.get(i);
            mysqlSql.append(cleanIdentifier(column.getColumnName()))
                    .append(" = ");
            mysqlSql.append(convertExpression(expression));
            if (i < columns.size() - 1) {
                mysqlSql.append(", ");
            }
        }

        Expression where = update.getWhere();
        if (where != null) {
            mysqlSql.append(" WHERE ").append(convertExpression(where));
        }

        mysqlSql.append(";\n\n");
    }

    @Override
    public void visit(Delete delete) {
        String tableName = cleanIdentifier(delete.getTable().getName());
        mysqlSql.append("DELETE FROM ").append(tableName);

        Expression where = delete.getWhere();
        if (where != null) {
            mysqlSql.append(" WHERE ").append(convertExpression(where));
        }

        mysqlSql.append(";\n\n");
    }

    @Override
    public void visit(Comment comment) {
        String commentText = comment.getComment().toString().replaceAll("^'|'$", "");
        if (comment.getTable() != null) {
            String tableName = cleanIdentifier(comment.getTable().getName());
            mysqlSql.append("ALTER TABLE ").append(tableName)
                    .append(" COMMENT='").append(escapeComment(commentText)).append("';\n");
        }
        mysqlSql.append("\n");
    }

    private String convertExpression(Expression expression) {
        if (expression == null) return "";

        if (expression instanceof Column) {
            Column column = (Column) expression;
            return cleanIdentifier(column.getColumnName());
        }
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

            return convertFunction(functionName, params);
        }
        if (expression instanceof EqualsTo) {
            EqualsTo equalsTo = (EqualsTo) expression;
            return convertExpression(equalsTo.getLeftExpression()) + " = " +
                    convertExpression(equalsTo.getRightExpression());
        }
        if (expression instanceof NotEqualsTo) {
            NotEqualsTo notEqualsTo = (NotEqualsTo) expression;
            return convertExpression(notEqualsTo.getLeftExpression()) + " != " +
                    convertExpression(notEqualsTo.getRightExpression());
        }
        if (expression instanceof GreaterThan) {
            GreaterThan greaterThan = (GreaterThan) expression;
            return convertExpression(greaterThan.getLeftExpression()) + " > " +
                    convertExpression(greaterThan.getRightExpression());
        }
        if (expression instanceof GreaterThanEquals) {
            GreaterThanEquals gte = (GreaterThanEquals) expression;
            return convertExpression(gte.getLeftExpression()) + " >= " +
                    convertExpression(gte.getRightExpression());
        }
        if (expression instanceof MinorThan) {
            MinorThan minorThan = (MinorThan) expression;
            return convertExpression(minorThan.getLeftExpression()) + " < " +
                    convertExpression(minorThan.getRightExpression());
        }
        if (expression instanceof MinorThanEquals) {
            MinorThanEquals lte = (MinorThanEquals) expression;
            return convertExpression(lte.getLeftExpression()) + " <= " +
                    convertExpression(lte.getRightExpression());
        }
        if (expression instanceof AndExpression) {
            AndExpression andExpr = (AndExpression) expression;
            return convertExpression(andExpr.getLeftExpression()) + " AND " +
                    convertExpression(andExpr.getRightExpression());
        }
        if (expression instanceof OrExpression) {
            OrExpression orExpr = (OrExpression) expression;
            return convertExpression(orExpr.getLeftExpression()) + " OR " +
                    convertExpression(orExpr.getRightExpression());
        }
        if (expression instanceof LikeExpression) {
            LikeExpression likeExpr = (LikeExpression) expression;
            String result = convertExpression(likeExpr.getLeftExpression()) + " LIKE " +
                    convertExpression(likeExpr.getRightExpression());
            if (likeExpr.isNot()) {
                result = "NOT " + result;
            }
            return result;
        }
        if (expression instanceof InExpression) {
            InExpression inExpr = (InExpression) expression;
            String result = convertExpression(inExpr.getLeftExpression()) +
                    (inExpr.isNot() ? " NOT IN " : " IN ") + "(";
            // getRightItemsList() may not exist or may not return ExpressionList
            Object rightItemsList = null;
            try {
                rightItemsList = InExpression.class.getMethod("getRightItemsList").invoke(inExpr);
            } catch (Exception ignore) {}
            if (rightItemsList instanceof ExpressionList) {
                @SuppressWarnings("unchecked")
                List<Expression> items = (List<Expression>) (List<?>) ((ExpressionList) rightItemsList).getExpressions();
                for (int i = 0; i < items.size(); i++) {
                    Expression obj = items.get(i);
                    result += convertExpression(obj);
                    if (i < items.size() - 1) {
                        result += ", ";
                    }
                }
            } else if (rightItemsList != null) {
                result += rightItemsList.toString();
            }
            result += ")";
            return result;
        }
        if (expression instanceof Parenthesis) {
            Parenthesis paren = (Parenthesis) expression;
            return "(" + convertExpression(paren.getExpression()) + ")";
        }
        if (expression instanceof CaseExpression) {
            CaseExpression caseExpr = (CaseExpression) expression;
            StringBuilder sb = new StringBuilder("CASE ");
            if (caseExpr.getSwitchExpression() != null) {
                sb.append(convertExpression(caseExpr.getSwitchExpression()));
            }
            List<?> whenClausesRaw = caseExpr.getWhenClauses();
            if (whenClausesRaw != null) {
                for (Object whenObj : whenClausesRaw) {
                    try {
                        Object whenExpr = whenObj.getClass().getMethod("getWhenExpression").invoke(whenObj);
                        Object thenExpr = whenObj.getClass().getMethod("getThenExpression").invoke(whenObj);
                        sb.append(" WHEN ").append(convertExpression((Expression)whenExpr))
                                .append(" THEN ").append(convertExpression((Expression)thenExpr));
                    } catch (Exception ignore) {}
                }
            }
            if (caseExpr.getElseExpression() != null) {
                sb.append(" ELSE ").append(convertExpression(caseExpr.getElseExpression()));
            }
            sb.append(" END");
            return sb.toString();
        }
        return expression.toString();
    }

    public String getMysqlSql() {
        return mysqlSql.toString();
    }

    public void clear() {
        mysqlSql.setLength(0);
        comments.clear();
        primaryKeys.clear();
        uniqueKeys.clear();
        columnComments.clear();
    }
}