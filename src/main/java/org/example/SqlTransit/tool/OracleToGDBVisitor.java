package org.example.SqlTransit.tool;

import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.alter.Alter;
import net.sf.jsqlparser.statement.alter.AlterExpression;

import net.sf.jsqlparser.statement.comment.Comment;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class OracleToGDBVisitor extends StatementVisitorAdapter {
    private final StringBuilder gdbSql = new StringBuilder();
    private final List<String> commentStatements = new ArrayList<>();

    // 清理并大写标识符（所有位置都大写，去引号）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
    }

    // 表名处理（去引号且大写，带schema也大写，形如 SCHEMA.TABLE）
    private String getFullTableName(Table table) {
        if (table == null) return "";
        String schema = table.getSchemaName();
        String name = table.getName();
        if (schema != null && !schema.isEmpty()) {
            return cleanIdentifier(schema) + "." + cleanIdentifier(name);
        } else {
            return cleanIdentifier(name);
        }
    }

    // Helper for strings like "NX_BUP"."APP_INFO_CONF" → NX_BUP.APP_INFO_CONF
    private String getFullTableNameStr(String raw) {
        if (raw == null) return null;
        String s = raw.replaceAll("^[`'\"]+|[`'\"]+$", "");
        return s.replaceAll("\"", "").toUpperCase().replaceAll("\\s+", "");
    }

    // 替换布尔字面量 'Y'/'N' → true/false（忽略字符串内）
    private String replaceBooleanLiteralsForGDB(String sql) {
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
            if (i + 3 <= sql.length() && sql.substring(i, i + 3).equalsIgnoreCase("'Y'")) {
                sb.append("true");
                i += 3;
                continue;
            } else if (i + 3 <= sql.length() && sql.substring(i, i + 3).equalsIgnoreCase("'N'")) {
                sb.append("false");
                i += 3;
                continue;
            }
            sb.append(ch);
            i++;
        }
        return sb.toString();
    }

    private String uppercaseWhereColumnNames(String sql) {
        // 可扩展, 当前直接返回原文
        return sql;
    }

    private String processWhereExpression(Expression where) {
        if (where == null) return "";
        String expr = where.toString();
        expr = expr.replace("SYSDATE", "NOW()").replace("CURRENT_TIMESTAMP", "NOW()");
        expr = replaceBooleanLiteralsForGDB(expr);
        expr = uppercaseWhereColumnNames(expr);
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
                        if (i + 2 < tableOptions.size() && "=".equals(tableOptions.get(i + 1).trim())) {
                            String comment = tableOptions.get(i + 2).trim();
                            return comment;
                        }
                        if (i + 1 < tableOptions.size()) {
                            String comment = tableOptions.get(i + 1).trim();
                            return comment;
                        }
                    }
                }
                for (String option : tableOptions) {
                    if ((option.contains("'") || option.contains("\"")) && option.length() > 2) {
                        return option.trim();
                    }
                }
            }
        } catch (Exception e) { }
        String s = createTable.toString();
        Pattern[] patterns = {
                Pattern.compile("COMMENT\\s*=\\s*'([^']+)'", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s*=\\s*\"([^\"]+)\"", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s+'([^']+)'", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s+\"([^\"]+)\"", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s*=\\s*([^,;)]+)", Pattern.CASE_INSENSITIVE),
                Pattern.compile("COMMENT\\s+([^,;)]+)", Pattern.CASE_INSENSITIVE)
        };
        for (Pattern pattern : patterns) {
            Matcher m = pattern.matcher(s);
            if (m.find()) {
                String comment = m.group(1).trim();
                if ((comment.startsWith("'") && comment.endsWith("'")) || (comment.startsWith("\"") && comment.endsWith("\""))) {
                    comment = comment.substring(1, comment.length() - 1);
                }
                return comment;
            }
        }
        return null;
    }

    private String convertColumnType(String oracleType, List<?> args) {
        String type = oracleType.toUpperCase();
        switch (type) {
            case "NUMBER":
                return "BIGINT";
            case "VARCHAR2":
            case "VARCHAR":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR(" + args.get(0) + ")";
                }
                return "VARCHAR";
            case "DATE":
            case "TIMESTAMP":
                return "DATETIME";
            case "CLOB":
                return "TEXT";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + args.get(0) + ")";
                }
                return type;
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

            if (c == '\'' && (i == 0 || input.charAt(i - 1) != '\\')) {
                inSingleQuotes = !inSingleQuotes;
                currentToken.append(c);
            } else if (c == '"' && (i == 0 || input.charAt(i - 1) != '\\')) {
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
    public void visit(CreateTable createTable) {
        // 输出表名/模式名均为大写, 不加引号
        String tableName;
        try {
            Table table = createTable.getTable();
            if (table != null && table.getSchemaName() != null && !table.getSchemaName().isEmpty()) {
                tableName = cleanIdentifier(table.getSchemaName()) + "." + cleanIdentifier(table.getName());
            } else {
                tableName = cleanIdentifier(createTable.getTable().getName());
            }
        } catch (Exception e) {
            tableName = cleanIdentifier(createTable.getTable().getName());
        }
        gdbSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();
        Set<String> tablePrimaryKeyCols = new LinkedHashSet<>();
        List<String> checkConstraints = new ArrayList<>();
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
            if (indexes != null) {
                for (Object idx : indexes) {
                    String idxStr = idx.toString().trim();
                    String idxStrUpper = idxStr.toUpperCase();
                    if (idxStrUpper.contains("PRIMARY KEY")) {
                        List<String> pkCols = null;
                        try {
                            java.lang.reflect.Method getColumnsNamesMethod = idx.getClass().getMethod("getColumnsNames");
                            Object pkColsObj = getColumnsNamesMethod.invoke(idx);
                            if (pkColsObj instanceof List) {
                                pkCols = (List<String>) pkColsObj;
                            }
                        } catch (Exception ignore) {}
                        if (pkCols == null) {
                            Pattern pkPattern = Pattern.compile(
                                    "PRIMARY KEY\\s*\\(([^)]+)\\)", Pattern.CASE_INSENSITIVE);
                            Matcher m = pkPattern.matcher(idxStrUpper);
                            if (m.find()) {
                                String cols = m.group(1);
                                String[] arr = cols.split(",");
                                pkCols = new ArrayList<>();
                                for (String c : arr) pkCols.add(c.replaceAll("[`'\"]", "").trim().toUpperCase());
                            }
                        }
                        if (pkCols != null) tablePrimaryKeyCols.addAll(pkCols);
                    } else if (idxStrUpper.contains("CHECK")) {
                        try {
                            java.lang.reflect.Method getExpressionMethod = idx.getClass().getMethod("getExpression");
                            Object expressionObj = getExpressionMethod.invoke(idx);
                            String checkExpr = null;
                            if (expressionObj != null) {
                                checkExpr = expressionObj.toString();
                            }
                            String checkName = "";
                            try {
                                java.lang.reflect.Method getNamePartsMethod = idx.getClass().getMethod("getNameParts");
                                Object namePartsObj = getNamePartsMethod.invoke(idx);
                                if (namePartsObj instanceof List) {
                                    List<?> nameParts = (List<?>) namePartsObj;
                                    if (!nameParts.isEmpty()) {
                                        checkName = nameParts.get(0).toString();
                                    }
                                }
                            } catch (Exception ignore) {
                                Pattern p = Pattern.compile("CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)", Pattern.CASE_INSENSITIVE);
                                Matcher m = p.matcher(idxStr);
                                if (m.find()) {
                                    checkName = m.group(1);
                                }
                            }
                            String constraintNameClause = "";
                            if (checkName != null && !checkName.trim().isEmpty()) {
                                constraintNameClause = "CONSTRAINT " + cleanIdentifier(checkName) + " ";
                            }
                            if (checkExpr != null && !checkExpr.trim().isEmpty()) {
                                checkConstraints.add(constraintNameClause + "CHECK " + checkExpr);
                            }
                        } catch (Exception ignore) {
                            Pattern p = Pattern.compile("CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*CHECK\\s*\\((.+)\\)", Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                            Matcher m = p.matcher(idxStr);
                            if (m.find()) {
                                String checkName = m.group(1) != null ? m.group(1) : "";
                                String checkExpr = m.group(2).trim();
                                String constraintNameClause = "";
                                if (!checkName.isEmpty()) {
                                    constraintNameClause = "CONSTRAINT " + cleanIdentifier(checkName) + " ";
                                }
                                checkConstraints.add(constraintNameClause + "CHECK (" + checkExpr + ")");
                            }
                        }
                    }
                }
            }
        } catch(Exception ignore) { }

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) gdbSql.append(",\n");
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

            boolean isPrimaryKey = false;
            boolean isNotNull = false;
            boolean isUnique = false;
            String defaultValStr = null;

            for (int j = 0; j < specs.size(); j++) {
                String spec = specs.get(j).toUpperCase().trim();
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
                if ("PRIMARY".equals(spec)) {
                    isPrimaryKey = true;
                } else if ("UNIQUE".equals(spec)) {
                    isUnique = true;
                } else if ("NOT".equals(spec)) {
                    isNotNull = true;
                } else if ("DEFAULT".equals(spec) && j + 1 < specs.size()) {
                    defaultValStr = specs.get(j + 1);
                    j++;
                }
            }

            // 如果表级主键包含该列，也视为主键（避免JSqlParser不还原inline PRIMARY KEY的bug）
            if (!isPrimaryKey && tablePrimaryKeyCols.contains(cleanIdentifier(col.getColumnName()))) {
                isPrimaryKey = true;
            }

            gdbSql.append("    ").append(colName).append(" ").append(colType);

            String constraintPart = col.toString().toUpperCase().trim();
            if (constraintPart.contains("NOT NULL")) {
                gdbSql.append(" NOT NULL");
            }

            if (defaultValStr != null) {
                defaultValStr = defaultValStr.trim();
                if (defaultValStr.contains("SYSDATE") || defaultValStr.contains("CURRENT_TIMESTAMP")) {
                    gdbSql.append(" DEFAULT NOW()");
                } else if (colType.equalsIgnoreCase("VARCHAR(1)") &&
                        ("'Y'".equalsIgnoreCase(defaultValStr) || "'N'".equalsIgnoreCase(defaultValStr))) {
                    gdbSql.append(" DEFAULT ").append("'Y'".equalsIgnoreCase(defaultValStr) ? "true" : "false");
                } else {
                    gdbSql.append(" DEFAULT ").append(defaultValStr);
                }
            }

            if (isPrimaryKey) {
                gdbSql.append(" PRIMARY KEY");
            } else {
                if (isUnique) gdbSql.append(" UNIQUE");
            }


            try {
                java.lang.reflect.Method getCommentMethod = ColumnDefinition.class.getMethod("getComment");
                Object commentObj = getCommentMethod.invoke(col);
                if (commentObj != null) {
                    String columnComment = commentObj.toString().trim();
                    if (!columnComment.isEmpty()) {
                        if ((columnComment.startsWith("'") && columnComment.endsWith("'")) ||
                                (columnComment.startsWith("\"") && columnComment.endsWith("\""))) {
                            columnComment = columnComment.substring(1, columnComment.length() - 1);
                        }
                        String escapedComment = columnComment.replace("'", "''");
                        commentStatements.add("COMMENT ON COLUMN " + tableName + "." + colName +
                                " IS '" + escapedComment + "';\n");
                    }
                }
            } catch (Exception e) {
                // 忽略
            }
        }

        // 处理表级外键、主键、唯一、CHECK约束
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
            if (indexes != null && !indexes.isEmpty()) {
                for (Object idx : indexes) {
                    String idxStr = idx.toString().trim();
                    String idxStrUpper = idxStr.toUpperCase();
                    if (idxStrUpper.contains("FOREIGN KEY")) {
                        Pattern fkPattern = Pattern.compile(
                                "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*FOREIGN KEY\\s*\\(([^)]+)\\)\\s*REFERENCES\\s+([`'\"]?[\\w\\.]+[`'\"]?)\\s*\\(([^)]+)\\)",
                                Pattern.CASE_INSENSITIVE);
                        Matcher m = fkPattern.matcher(idxStr);
                        if (m.find()) {
                            String fkName = m.group(1) == null ? "" : m.group(1);
                            String localCols = m.group(2);
                            String refTable = m.group(3);
                            String refCols = m.group(4);

                            gdbSql.append(",\n    ");
                            gdbSql.append("CONSTRAINT ");
                            if (fkName != null && !fkName.isEmpty()) {
                                gdbSql.append(cleanIdentifier(fkName)).append(" ");
                            }
                            gdbSql.append("FOREIGN KEY (")
                                    .append(parseAndJoinCols(localCols))
                                    .append(") REFERENCES ")
                                    .append(getFullTableNameStr(refTable))
                                    .append(" (")
                                    .append(parseAndJoinCols(refCols))
                                    .append(")");
                        }
                    } else if (idxStrUpper.contains("PRIMARY KEY")) {
                        Pattern pkPattern = Pattern.compile(
                                "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*PRIMARY KEY\\s*\\(([^)]+)\\)",
                                Pattern.CASE_INSENSITIVE);
                        Matcher m = pkPattern.matcher(idxStr);
                        if (m.find()) {
                            String pkName = m.group(1) == null ? "" : m.group(1);
                            String cols = m.group(2);

                            String[] pkColsArr = cols.split(",");
                            boolean shouldPrintPK = true;
                            if (pkColsArr.length == 1) {
                                if (tablePrimaryKeyCols.contains(cleanIdentifier(pkColsArr[0]))) {
                                    shouldPrintPK = false;
                                }
                            }
                            if (shouldPrintPK) {
                                gdbSql.append(",\n    ");
                                gdbSql.append("CONSTRAINT ");
                                if (pkName != null && !pkName.isEmpty()) {
                                    gdbSql.append(cleanIdentifier(pkName)).append(" ");
                                }
                                gdbSql.append("PRIMARY KEY (")
                                        .append(parseAndJoinCols(cols))
                                        .append(")");
                            }
                        }
                    } else if (idxStrUpper.contains("UNIQUE")) {
                        Pattern uqPattern = Pattern.compile(
                                "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*UNIQUE\\s*\\(([^)]+)\\)",
                                Pattern.CASE_INSENSITIVE);
                        Matcher m = uqPattern.matcher(idxStr);
                        if (m.find()) {
                            String uqName = m.group(1) == null ? "" : m.group(1);
                            String cols = m.group(2);
                            gdbSql.append(",\n    ");
                            gdbSql.append("CONSTRAINT ");
                            if (uqName != null && !uqName.isEmpty()) {
                                gdbSql.append(cleanIdentifier(uqName)).append(" ");
                            }
                            gdbSql.append("UNIQUE (").append(parseAndJoinCols(cols)).append(")");
                        }
                    }
                }
            }
        } catch (Exception e) {}

        if (!checkConstraints.isEmpty()) {
            for (String c : checkConstraints) {
                gdbSql.append(",\n    ").append(c);
            }
        }

        gdbSql.append("\n);\n\n");

        try {
            java.lang.reflect.Method getCommentMethod = CreateTable.class.getMethod("getComment");
            Object commentObj = getCommentMethod.invoke(createTable);
            if (commentObj != null && !commentObj.toString().trim().isEmpty()) {
                String tableComment = commentObj.toString().trim();
                if ((tableComment.startsWith("'") && tableComment.endsWith("'")) ||
                        (tableComment.startsWith("\"") && tableComment.endsWith("\""))) {
                    tableComment = tableComment.substring(1, tableComment.length() - 1);
                }
                tableComment = tableComment.replace("'", "''");
                commentStatements.add("COMMENT ON TABLE " + tableName + " IS '" + tableComment + "';\n");
            } else {
                String tableComment2 = extractTableComment(createTable);
                if (tableComment2 != null && !tableComment2.isEmpty()) {
                    tableComment2 = tableComment2.trim();
                    if ((tableComment2.startsWith("'") && tableComment2.endsWith("'")) ||
                            (tableComment2.startsWith("\"") && tableComment2.endsWith("\""))) {
                        tableComment2 = tableComment2.substring(1, tableComment2.length() - 1);
                    }
                    tableComment2 = tableComment2.replace("'", "''");
                    commentStatements.add("COMMENT ON TABLE " + tableName + " IS '" + tableComment2 + "';\n");
                }
            }
        } catch (Exception e) {
            String tableComment2 = extractTableComment(createTable);
            if (tableComment2 != null && !tableComment2.isEmpty()) {
                tableComment2 = tableComment2.trim();
                if ((tableComment2.startsWith("'") && tableComment2.endsWith("'")) ||
                        (tableComment2.startsWith("\"") && tableComment2.endsWith("\""))) {
                    tableComment2 = tableComment2.substring(1, tableComment2.length() - 1);
                }
                tableComment2 = tableComment2.replace("'", "''");
                commentStatements.add("COMMENT ON TABLE " + tableName + " IS '" + tableComment2 + "';\n");
            }
        }

        if (!commentStatements.isEmpty()) {
            for (String cmt : commentStatements) {
                gdbSql.append(cmt);
            }
            commentStatements.clear();
        }
    }

    @Override
    public void visit(Comment comment) {
        String commentStr = comment.toString();
        StringBuilder builder = new StringBuilder("COMMENT ON ");
        Pattern tablePattern = Pattern.compile(
                "^\\s*COMMENT\\s+ON\\s+TABLE\\s+(\\S+)\\s+IS\\s+(['\"])(.*?)\\2",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher tableMatcher = tablePattern.matcher(commentStr);
        if (tableMatcher.find()) {
            String table = tableMatcher.group(1).replaceAll("^[`'\"]+|[`'\"]+$", "");
            String commentTxt = tableMatcher.group(3);
            commentTxt = commentTxt.replace("'", "''");
            builder.append("TABLE ").append(table.toUpperCase()).append(" IS '").append(commentTxt).append("';\n");
            gdbSql.append(builder);
            return;
        }
        Pattern colPattern = Pattern.compile(
                "^\\s*COMMENT\\s+ON\\s+COLUMN\\s+(\\S+)\\s+IS\\s+(['\"])(.*?)\\2",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher colMatcher = colPattern.matcher(commentStr);
        if (colMatcher.find()) {
            String col = colMatcher.group(1).replaceAll("^[`'\"]+|[`'\"]+$", "");
            String commentTxt = colMatcher.group(3);
            commentTxt = commentTxt.replace("'", "''");
            builder.append("COLUMN ").append(col.toUpperCase()).append(" IS '").append(commentTxt).append("';\n");
            gdbSql.append(builder);
            return;
        }
        builder.append(commentStr).append(";\n");
        gdbSql.append(builder);
    }

    // 列名参数全部大写且无引号（形如ID, CODE...）
    private String parseAndJoinCols(String cols) {
        if (cols == null) return "";
        String[] arr = cols.split(",");
        List<String> result = new ArrayList<>();
        for (String c : arr) {
            c = c.trim().replaceAll("^[`'\"]+|[`'\"]+$", "");
            result.add(c.toUpperCase());
        }
        return String.join(", ", result);
    }

    @Override
    public void visit(CreateIndex createIndex) {
        String indexName;
        try {
            indexName = cleanIdentifier(createIndex.getIndex().getName());
        } catch (Exception e) {
            indexName = cleanIdentifier(createIndex.getIndex().getName());
        }
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
            java.lang.reflect.Method isUniqueMethod = createIndex.getClass().getMethod("isUnique");
            Object result = isUniqueMethod.invoke(createIndex);
            if (result instanceof Boolean) isUnique = (Boolean) result;
        } catch (Exception e) {
            String text = createIndex.toString().toUpperCase();
            if (text.contains("UNIQUE") || (indexName != null && indexName.startsWith("UNIQUE_"))) {
                isUnique = true;
            }
        }

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
                    if (!clean.isEmpty()) {
                        columns.add(clean.toUpperCase());
                    }
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

        gdbSql.append("CREATE");
        if (isUnique) gdbSql.append(" UNIQUE");
        gdbSql.append(" INDEX ").append(indexName)
                .append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(");\n\n");
    }

    @Override
    public void visit(Alter alter) {
        String tableName = null;
        try {
            java.lang.reflect.Method getTableMethod = Alter.class.getMethod("getTable");
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
            String alterStr = alter.toString();
            Pattern p = Pattern.compile("ALTER TABLE\\s+((\"[^\"]+\"\\.)?\"[^\"]+\")", Pattern.CASE_INSENSITIVE);
            Matcher m = p.matcher(alterStr);
            if (m.find()) {
                String t = m.group(1);
                t = t.replaceAll("^[`'\"]+|[`'\"]+$", "");
                tableName = t.replaceAll("\"", "").toUpperCase();
            }
            if (tableName == null) {
                Pattern p2 = Pattern.compile("ALTER TABLE\\s+([\\w\\[\\]]+)", Pattern.CASE_INSENSITIVE);
                Matcher m2 = p2.matcher(alterStr);
                if (m2.find()) {
                    tableName = m2.group(1).toUpperCase();
                }
            }
        }
        if (tableName == null) {
            tableName = "UNKNOWN_TABLE";
        }
        List<AlterExpression> expressions = null;
        try {
            java.lang.reflect.Method getAlterExprMethod = Alter.class.getMethod("getAlterExpressions");
            Object alterExprsObj = getAlterExprMethod.invoke(alter);
            if (alterExprsObj instanceof List) {
                expressions = (List<AlterExpression>)alterExprsObj;
            }
        } catch (Exception e) { }
        if (expressions != null) {
            for (AlterExpression expr : expressions) {
                if (expr == null) continue;
                String opStr = expr.getOperation() != null ? expr.getOperation().toString().toUpperCase() : "";
                if ("ADD".equals(opStr) && expr.getIndex() != null) {
                    Object idx = expr.getIndex();
                    String idxStr = idx.toString();
                    String idxStrUpper = idxStr.toUpperCase();
                    Pattern pkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*PRIMARY KEY\\s*\\(([^)]+)\\)",
                            Pattern.CASE_INSENSITIVE);
                    Matcher pkMatcher = pkPattern.matcher(idxStr);
                    if (pkMatcher.find()) {
                        String pkName = pkMatcher.group(1) == null ? "" : pkMatcher.group(1);
                        String cols = pkMatcher.group(2);
                        gdbSql.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (pkName != null && !pkName.isEmpty()) {
                            gdbSql.append(cleanIdentifier(pkName)).append(" ");
                        }
                        gdbSql.append("PRIMARY KEY (")
                                .append(parseAndJoinCols(cols))
                                .append(");\n\n");
                        continue;
                    }
                    Pattern uqPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*UNIQUE\\s*\\(([^)]+)\\)",
                            Pattern.CASE_INSENSITIVE);
                    Matcher uqMatcher = uqPattern.matcher(idxStr);
                    if (uqMatcher.find()) {
                        String uqName = uqMatcher.group(1) == null ? "" : uqMatcher.group(1);
                        String cols = uqMatcher.group(2);
                        gdbSql.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (uqName != null && !uqName.isEmpty()) {
                            gdbSql.append(cleanIdentifier(uqName)).append(" ");
                        }
                        gdbSql.append("UNIQUE (")
                                .append(parseAndJoinCols(cols))
                                .append(");\n\n");
                        continue;
                    }
                    Pattern fkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*FOREIGN KEY\\s*\\(([^)]+)\\)\\s*REFERENCES\\s+([`'\"]?[\\w\\.]+[`'\"]?)\\s*\\(([^)]+)\\)",
                            Pattern.CASE_INSENSITIVE);
                    Matcher fkMatcher = fkPattern.matcher(idxStr);
                    if (fkMatcher.find()) {
                        String fkName = fkMatcher.group(1) == null ? "" : fkMatcher.group(1);
                        String localCols = fkMatcher.group(2);
                        String refTable = fkMatcher.group(3);
                        String refCols = fkMatcher.group(4);
                        gdbSql.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (fkName != null && !fkName.isEmpty()) {
                            gdbSql.append(cleanIdentifier(fkName)).append(" ");
                        }
                        gdbSql.append("FOREIGN KEY (")
                                .append(parseAndJoinCols(localCols))
                                .append(") REFERENCES ")
                                .append(getFullTableNameStr(refTable))
                                .append(" (")
                                .append(parseAndJoinCols(refCols))
                                .append(");\n\n");
                        continue;
                    }
                    Pattern checkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*CHECK\\s*\\((.+)\\)", Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                    Matcher checkMatcher = checkPattern.matcher(idxStr);
                    if (checkMatcher.find()) {
                        String checkName = checkMatcher.group(1) == null ? "" : checkMatcher.group(1);
                        String checkExpr = checkMatcher.group(2).trim();
                        gdbSql.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CONSTRAINT ");
                        if (checkName != null && !checkName.isEmpty()) {
                            gdbSql.append(cleanIdentifier(checkName)).append(" ");
                        }
                        gdbSql.append("CHECK (").append(checkExpr).append(");\n\n");
                        continue;
                    }
                }
            }
        } else {
            String s = alter.toString();
            gdbSql.append(s).append(";\n\n");
        }
    }

    @Override
    public void visit(Insert insert) {
        String tableName;
        try {
            Table table = insert.getTable();
            if (table != null && table.getSchemaName() != null && !table.getSchemaName().isEmpty()) {
                tableName = cleanIdentifier(table.getSchemaName()) + "." + cleanIdentifier(table.getName());
            } else {
                tableName = cleanIdentifier(insert.getTable().getName());
            }
        } catch (Exception e) {
            tableName = cleanIdentifier(insert.getTable().getName());
        }
        gdbSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            gdbSql.append("(");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                gdbSql.append(colName);
                if (i < columns.size() - 1) gdbSql.append(", ");
            }
            gdbSql.append(")");
        }

        String valuesStr = insert.toString().toUpperCase();
        int valuesIdx = valuesStr.indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = insert.toString().substring(valuesIdx + 6);
            valuesPart = valuesPart.replace("SYSDATE", "NOW()");
            valuesPart = valuesPart.replace("CURRENT_TIMESTAMP", "NOW()");
            valuesPart = replaceBooleanLiteralsForGDB(valuesPart);
        }

        gdbSql.append(" VALUES").append(valuesPart).append(";\n\n");
    }

    @Override
    public void visit(Update update) {
        String tableName;
        try {
            Table table = update.getTable();
            if (table != null && table.getSchemaName() != null && !table.getSchemaName().isEmpty()) {
                tableName = cleanIdentifier(table.getSchemaName()) + "." + cleanIdentifier(table.getName());
            } else {
                tableName = cleanIdentifier(update.getTable().getName());
            }
        } catch (Exception e) {
            tableName = cleanIdentifier(update.getTable().getName());
        }
        gdbSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = valueExpr.replace("SYSDATE", "NOW()");
            valueExpr = valueExpr.replace("CURRENT_TIMESTAMP", "NOW()");
            valueExpr = replaceBooleanLiteralsForGDB(valueExpr);
            gdbSql.append(colName).append("=").append(valueExpr);
            if (i < cols.size() - 1) gdbSql.append(", ");
        }
        gdbSql.append(processWhereExpression(update.getWhere())).append(";\n\n");
    }

    @Override
    public void visit(Delete delete) {
        String tableName;
        try {
            Table table = delete.getTable();
            if (table != null && table.getSchemaName() != null && !table.getSchemaName().isEmpty()) {
                tableName = cleanIdentifier(table.getSchemaName()) + "." + cleanIdentifier(table.getName());
            } else {
                tableName = cleanIdentifier(delete.getTable().getName());
            }
        } catch (Exception e) {
            tableName = cleanIdentifier(delete.getTable().getName());
        }
        gdbSql.append("DELETE FROM ").append(tableName);
        gdbSql.append(processWhereExpression(delete.getWhere())).append(";\n\n");
    }

    public String getGdbSql() {
        return gdbSql.toString();
    }
}