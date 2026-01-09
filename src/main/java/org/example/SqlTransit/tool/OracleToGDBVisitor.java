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
    private enum ChunkType { CREATE_TABLE, RAW }

    private static class Chunk {
        final ChunkType type;
        final CreateTable createTable;
        final String rawSql;
        Chunk(CreateTable createTable) {
            this.type = ChunkType.CREATE_TABLE;
            this.createTable = createTable;
            this.rawSql = null;
        }
        Chunk(String rawSql) {
            this.type = ChunkType.RAW;
            this.createTable = null;
            this.rawSql = rawSql;
        }
    }

    private final List<Chunk> chunks = new ArrayList<>();
    private final Map<String, String> columnComments = new HashMap<>(); // 存储列注释：table.column -> comment
    private final Map<String, String> tableComments = new HashMap<>(); // 存储表注释：table -> comment
    private final Map<String, Set<String>> tablePkColsMap = new HashMap<>(); // 表主键列集合，去模式名，用于去重索引
    private String currentTableName = null; // 当前处理的表名

    private void addRawSql(String sql) {
        if (sql != null && !sql.isEmpty()) {
            chunks.add(new Chunk(sql));
        }
    }

    // 清理标识符并添加反引号（小写）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        String cleaned = name.replaceAll("^[`'\"]+|[`'\"]+$", "").toLowerCase();
        return "`" + cleaned + "`";
    }

    // 获取表的完整名称（小写，带schema）
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

    // 处理表名字符串，去掉schema部分，返回小写表名
    private String getTableNameOnly(String raw) {
        if (raw == null) return null;
        // 去掉引号
        String s = raw.replaceAll("[`'\"]", "");
        // 按点分割，取最后一部分作为表名
        String[] parts = s.split("\\.");
        String tableName = parts.length > 0 ? parts[parts.length - 1] : s;
        return tableName.toLowerCase();
    }

    // 去掉schema并清洗名称，返回带反引号的小写索引名
    private String cleanIdentifierNoSchema(String name) {
        if (name == null) return null;
        String cleaned = name.replaceAll("[`'\"]", "");
        if (cleaned.contains(".")) {
            cleaned = cleaned.substring(cleaned.lastIndexOf(".") + 1);
        }
        cleaned = cleaned.trim().toLowerCase();
        return "`" + cleaned + "`";
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
            case "NUMBER": {
                Integer p = null;
                Integer s = null;
                try {
                    if (args != null && args.size() >= 1 && args.get(0) != null) {
                        p = Integer.parseInt(args.get(0).toString());
                    }
                    if (args != null && args.size() >= 2 && args.get(1) != null) {
                        s = Integer.parseInt(args.get(1).toString());
                    }
                } catch (NumberFormatException ignored) {}

                // 精确规则
                if (p != null && (p == 1) && (s == null || s == 0)) {
                    return "TINYINT(1)";
                }
                if (p != null && s != null && s > 0) {
                    return "DECIMAL(" + p + "," + s + ")";
                }
                if (p != null && p == 10 && (s == null || s == 0)) {
                    return "DOUBLE";
                }
                if (p != null && p <= 9 && (s == null || s == 0)) {
                    return "INT(" + p + ")";
                }
                if (p != null && p > 10 && (s == null || s == 0)) {
                return "BIGINT";
                }
                return "DOUBLE";
            }
            case "VARCHAR2":
            case "VARCHAR":
                if (args != null && !args.isEmpty() && args.get(0) != null) {
                    String lenStr = args.get(0).toString().trim();
                    try {
                        int len = Integer.parseInt(lenStr);
                        if (len >= 1000) {
                            // 长度大于等于 1000，统一转为 TEXT
                            return "TEXT";
                        } else {
                            return "VARCHAR(" + len + ")";
                        }
                    } catch (NumberFormatException e) {
                        // 非数字长度参数，回退为原始形式
                        return "VARCHAR(" + lenStr + ")";
                    }
                }
                return "VARCHAR";
            case "DATE":
                return "DATETIME";
            case "TIMESTAMP":
                if (args != null && !args.isEmpty()) {
                    return "DATETIME(" + args.get(0) + ")";
                }
                return "DATETIME";
            case "NCLOB":
                return "LONGTEXT";
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
        // 延迟渲染，先缓存 AST，最终在 getGdbSql 时统一输出，以便后置 COMMENT 也能内联
        // 同时预先记录主键列集合，供后续索引去重判断使用
        try {
            Table table = createTable.getTable();
            String tableName = cleanIdentifier(table.getName());
        Set<String> tablePrimaryKeyCols = new LinkedHashSet<>();
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
            if (indexes != null) {
                for (Object idx : indexes) {
                    String idxStr = idx.toString().trim();
                    String idxStrUpper = idxStr.toUpperCase();
                    if (idxStrUpper.contains("PRIMARY KEY")) {
                            List<String> pkCols = extractColumnNamesFromConstraint(idxStr);
                            if (pkCols != null && !pkCols.isEmpty()) {
                                tablePrimaryKeyCols.addAll(pkCols);
                            }
                        }
                    }
                }
            } catch (Exception ignore) { }
            if (!tablePrimaryKeyCols.isEmpty()) {
                Set<String> pkSet = new LinkedHashSet<>();
                for (String c : tablePrimaryKeyCols) {
                    pkSet.add(c.replace("`", ""));
                }
                String normTableKey = tableName.replace("`", "");
                tablePkColsMap.put(normTableKey, pkSet);
                            }
        } catch (Exception ignore) { }

        chunks.add(new Chunk(createTable));
    }

    @Override
    public void visit(Comment comment) {
        String commentStr = comment.toString();

        // 处理表注释
        Pattern tablePattern = Pattern.compile(
                "^\\s*COMMENT\\s+ON\\s+TABLE\\s+([^\\s]+)\\s+IS\\s+(['\"])(.*?)\\2",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher tableMatcher = tablePattern.matcher(commentStr);
        if (tableMatcher.find()) {
            String table = tableMatcher.group(1);
            String commentTxt = tableMatcher.group(3);

            // 获取表名（去掉schema）
            String tableName = getTableNameOnly(table);

            // 存储到Map中，等待CREATE TABLE时使用
            tableComments.put(tableName, commentTxt);

            return;
        }

        // 处理列注释
        Pattern colPattern = Pattern.compile(
                "^\\s*COMMENT\\s+ON\\s+COLUMN\\s+([^\\s]+)\\s+IS\\s+(['\"])(.*?)\\2",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher colMatcher = colPattern.matcher(commentStr);
        if (colMatcher.find()) {
            String column = colMatcher.group(1);
            String commentTxt = colMatcher.group(3);

            // 解析表名和列名
            String[] parts = column.split("\\.");
            if (parts.length >= 2) {
                String tableName, columnName;
                if (parts.length == 2) {
                    // table.column 格式
                    tableName = parts[0];
                    columnName = parts[1];
            } else {
                    // schema.table.column 格式
                    tableName = parts[1];
                    columnName = parts[2];
                }

                // 清理名称
                tableName = getTableNameOnly(tableName);
                columnName = columnName.replaceAll("[`'\"]", "").toLowerCase();

                // 存储到Map中，等待CREATE TABLE时使用
                String commentKey = tableName + "." + columnName;
                columnComments.put(commentKey, commentTxt);

            }
            return;
        }

        // 其他注释格式，直接输出
        addRawSql(commentStr + ";\n");
    }

    // 列名参数全部小写且带反引号（形如`id`, `code`...）
    private String parseAndJoinCols(String cols) {
        if (cols == null) return "";
                                String[] arr = cols.split(",");
        List<String> result = new ArrayList<>();
        for (String c : arr) {
            result.add(cleanIdentifier(c.trim()));
        }
        return String.join(", ", result);
    }

    @Override
    public void visit(CreateIndex createIndex) {
        String indexName;
        try {
            indexName = cleanIdentifierNoSchema(createIndex.getIndex().getName());
        } catch (Exception e) {
            indexName = cleanIdentifierNoSchema(createIndex.getIndex().getName());
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
            if (text.contains("UNIQUE") || (indexName != null && indexName.toUpperCase().contains("UNIQUE"))) {
                isUnique = true;
            }
        }

        List<String> columns = extractIndexColumns(createIndex);

        // 如果是唯一索引且列集合与表主键一致，跳过创建（避免重复）
        String normTableKey = tableName.replace("`", "");
        Set<String> pkCols = tablePkColsMap.get(normTableKey);
        if (isUnique && pkCols != null && !pkCols.isEmpty()) {
            Set<String> idxCols = new LinkedHashSet<>();
            for (String c : columns) {
                idxCols.add(c.replace("`", ""));
            }
            if (pkCols.equals(idxCols)) {
                return;
            }
        }

        StringBuilder sb = new StringBuilder();
        sb.append("CREATE");
        if (isUnique) sb.append(" UNIQUE");
        sb.append(" INDEX ").append(indexName)
                .append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(");\n\n");
        addRawSql(sb.toString());
    }

    // 辅助方法：获取列规范（模仿 OracleToMysqlVisitor，实现对 DEFAULT / NOT NULL 的完整保留）
    private List<String> getColumnSpecs(ColumnDefinition col) {
        List<String> specs = new ArrayList<>();
        try {
            // 优先使用 JSqlParser 提供的 getColumnSpecs（适配当前版本）
            java.lang.reflect.Method method = ColumnDefinition.class.getMethod("getColumnSpecs");
            @SuppressWarnings("unchecked")
            List<String> columnSpecs = (List<String>) method.invoke(col);
            if (columnSpecs != null) {
                specs.addAll(columnSpecs);
            }
        } catch (Exception e) {
            // 回退：从 toString() 中解析出类型后面的约束片段并切分
            String colStr = col.toString();
            int typeEnd = colStr.indexOf(" ", col.getColumnName().length() + 1);
            if (typeEnd > 0) {
                String constraintPart = colStr.substring(typeEnd).trim();
                // 兼容带引号的 token：如 DEFAULT 'x' NOT NULL / COMMENT 'xxx'
                Pattern pattern = Pattern.compile("([^\\s'\"]+|\"[^\"]*\"|'[^']*')");
                Matcher matcher = pattern.matcher(constraintPart);
                while (matcher.find()) {
                    specs.add(matcher.group());
                }
            }
        }
        return specs;
    }

    // 辅助方法：提取约束中的列名
    private List<String> extractColumnNamesFromConstraint(String constraintStr) {
        List<String> columns = new ArrayList<>();
        Pattern pattern = Pattern.compile("\\(([^)]+)\\)");
        Matcher matcher = pattern.matcher(constraintStr);
        if (matcher.find()) {
            String cols = matcher.group(1);
            String[] colArray = cols.split(",");
            for (String col : colArray) {
                String cleanCol = col.replaceAll("[`'\"]", "").trim().toLowerCase();
                if (!cleanCol.isEmpty()) {
                    columns.add(cleanCol);
                }
            }
        }
        return columns;
                    }

    // 辅助方法：提取CHECK约束
    private String extractCheckConstraint(String constraintStr) {
        // 匹配两种格式：
        // 1. CONSTRAINT name CHECK (...)
        // 2. CHECK (...) （没有约束名）
        Pattern pattern = Pattern.compile(
                "(?:CONSTRAINT\\s+([`'\"]?[\\w_]+[`'\"]?)\\s+)?CHECK\\s*\\((.+?)\\)",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher matcher = pattern.matcher(constraintStr);
        if (matcher.find()) {
            String checkName = matcher.group(1);
            String checkExpr = matcher.group(2).trim();

            // 检查是否是 IS NOT NULL（应该已经被处理）
            if (checkExpr.toUpperCase().contains("IS NOT NULL")) {
                return null;
            }

            // 只有约束名存在且不为空且不是 "null" 时才添加约束名
            String constraintNameClause = "";
            if (checkName != null && !checkName.trim().isEmpty() &&
                !checkName.trim().equalsIgnoreCase("null") &&
                !checkName.replaceAll("[`'\"]", "").trim().equalsIgnoreCase("null")) {
                constraintNameClause = "CONSTRAINT " + cleanIdentifier(checkName) + " ";
            }
            return constraintNameClause + "CHECK (" + checkExpr + ")";
        }
        return null;
    }

    // 辅助方法：添加表级约束
    private void addTableConstraints(CreateTable createTable, String tableName,
                                     Set<String> tablePrimaryKeyCols, List<String> checkConstraints,
                                     StringBuilder sb) {
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
            if (indexes != null && !indexes.isEmpty()) {
                for (Object idx : indexes) {
                    String idxStr = idx.toString().trim();
                    String idxStrUpper = idxStr.toUpperCase();

                    if (idxStrUpper.contains("FOREIGN KEY")) {
                        addForeignKeyConstraint(idxStr, tableName, sb);
                    } else if (idxStrUpper.contains("PRIMARY KEY")) {
                        addPrimaryKeyConstraint(idxStr, tableName, tablePrimaryKeyCols, sb);
                    } else if (idxStrUpper.contains("UNIQUE")) {
                        addUniqueConstraint(idxStr, tableName, sb);
                    }
                }
            }
        } catch (Exception e) {}

        // 添加CHECK约束
        if (!checkConstraints.isEmpty()) {
            for (String c : checkConstraints) {
                sb.append(",\n    ").append(c);
            }
        }
    }

    // 辅助方法：添加外键约束
    private void addForeignKeyConstraint(String constraintStr, String tableName, StringBuilder sb) {
        // 改进正则表达式以更好地匹配Oracle格式的外键约束（包括schema.table格式和可能的换行）
        // 匹配格式：CONSTRAINT "name" FOREIGN KEY ("cols") REFERENCES "schema"."table" ("cols")
        // 使用更灵活的正则，先匹配到REFERENCES后面的表名（可能包含schema.table格式）
        Pattern pattern = Pattern.compile(
            "CONSTRAINT\\s+([`'\"][^`'\"]+[`'\"]|[\\w_]+)?\\s*FOREIGN\\s+KEY\\s*\\(([^)]+)\\)\\s*REFERENCES\\s+([^\\s(]+)\\s*\\(([^)]+)\\)",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher matcher = pattern.matcher(constraintStr);
        if (matcher.find()) {
            String fkName = matcher.group(1);
            String localCols = matcher.group(2);
            String refTable = matcher.group(3);
            String refCols = matcher.group(4);

            sb.append(",\n    CONSTRAINT ");
            if (fkName != null && !fkName.trim().isEmpty()) {
                sb.append(cleanIdentifier(fkName.trim())).append(" ");
                            }
            sb.append("FOREIGN KEY (")
                                    .append(parseAndJoinCols(localCols))
                                    .append(") REFERENCES ")
                    .append(cleanIdentifier(getTableNameOnly(refTable)))
                                    .append(" (")
                                    .append(parseAndJoinCols(refCols))
                                    .append(")");
                        }
    }

    // 辅助方法：添加主键约束
    private void addPrimaryKeyConstraint(String constraintStr, String tableName, Set<String> tablePrimaryKeyCols, StringBuilder sb) {
        Pattern pattern = Pattern.compile(
                                "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*PRIMARY KEY\\s*\\(([^)]+)\\)",
                                Pattern.CASE_INSENSITIVE);
        Matcher matcher = pattern.matcher(constraintStr);
        if (matcher.find()) {
            String pkName = matcher.group(1);
            String cols = matcher.group(2);

                            String[] pkColsArr = cols.split(",");
                            boolean shouldPrintPK = true;
                            if (pkColsArr.length == 1) {
                String singleCol = cleanIdentifier(pkColsArr[0]).replace("`", "");
                if (tablePrimaryKeyCols.contains(singleCol)) {
                                    shouldPrintPK = false;
                                }
                            }
                            if (shouldPrintPK) {
                sb.append(",\n    CONSTRAINT ");
                                if (pkName != null && !pkName.isEmpty()) {
                    sb.append(cleanIdentifier(pkName)).append(" ");
                                }
                sb.append("PRIMARY KEY (")
                                        .append(parseAndJoinCols(cols))
                                        .append(")");
                            }
                        }
    }

    // 辅助方法：添加唯一约束
    private void addUniqueConstraint(String constraintStr, String tableName, StringBuilder sb) {
        Pattern pattern = Pattern.compile(
                                "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*UNIQUE\\s*\\(([^)]+)\\)",
                                Pattern.CASE_INSENSITIVE);
        Matcher matcher = pattern.matcher(constraintStr);
        if (matcher.find()) {
            String uqName = matcher.group(1);
            String cols = matcher.group(2);
            sb.append(",\n    CONSTRAINT ");
                            if (uqName != null && !uqName.isEmpty()) {
                sb.append(cleanIdentifier(uqName)).append(" ");
                            }
            sb.append("UNIQUE (").append(parseAndJoinCols(cols)).append(")");
                        }
                    }

    // 渲染 CREATE TABLE（延迟执行，确保 COMMENT 顺序无关）
    private String renderCreateTable(CreateTable createTable) {
        StringBuilder sb = new StringBuilder();

        Table table = createTable.getTable();
        // 如果存在 schema，则保留 schema.table
        String tableName = getFullTableName(table);
        currentTableName = tableName;
        sb.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();
        Set<String> tablePrimaryKeyCols = new LinkedHashSet<>();
        Map<String, Boolean> columnNotNullMap = new HashMap<>();
        List<String> checkConstraints = new ArrayList<>();

        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
            if (indexes != null) {
                for (Object idx : indexes) {
                    String idxStr = idx.toString().trim();
                    String idxStrUpper = idxStr.toUpperCase();
                    if (idxStrUpper.contains("PRIMARY KEY")) {
                        List<String> pkCols = extractColumnNamesFromConstraint(idxStr);
                        if (pkCols != null && !pkCols.isEmpty()) {
                            tablePrimaryKeyCols.addAll(pkCols);
                        }
                    } else if (idxStrUpper.contains("CHECK")) {
                        // 处理 CHECK (column IS NOT NULL) 格式
                        Pattern isNotNullPattern = Pattern.compile(
                                "CHECK\\s*\\(\\s*\"?([^\"]+)\"?\\s+IS\\s+NOT\\s+NULL\\s*\\)", Pattern.CASE_INSENSITIVE);
                        Matcher isNotNullMatcher = isNotNullPattern.matcher(idxStr);
                        if (isNotNullMatcher.find()) {
                            String colName = isNotNullMatcher.group(1).replaceAll("[`'\"]", "").trim().toLowerCase();
                            columnNotNullMap.put(colName, true);
                        } else {
                            // 处理 CHECK (column IN (1,0)) ENABLE 格式
                            // 如果带 ENABLE，则：1) 标记字段为 NOT NULL，2) 同时保留 CHECK 约束
                            Pattern inPattern = Pattern.compile(
                                    "CHECK\\s*\\(\\s*([`'\"][^`'\"]+[`'\"]|[\\w_]+)\\s+IN\\s*\\(([^)]+)\\)\\s*\\)\\s+ENABLE",
                                    Pattern.CASE_INSENSITIVE);
                            Matcher inMatcher = inPattern.matcher(idxStr);
                            if (inMatcher.find()) {
                                String colName = inMatcher.group(1).replaceAll("[`'\"]", "").trim().toLowerCase();
                                String inValues = inMatcher.group(2).trim();
                                // 标记字段为 NOT NULL
                                columnNotNullMap.put(colName, true);
                                // 格式化 IN 值（在逗号后添加空格，如 "1,0" -> "1, 0"）
                                String formattedInValues = inValues.replaceAll(",\\s*", ", ");
                                // 添加 CHECK 约束（带反引号的列名）
                                String cleanColName = "`" + colName + "`";
                                checkConstraints.add("CONSTRAINT CHECK (" + cleanColName + " IN (" + formattedInValues + "))");
                            } else {
                                // 其他 CHECK 约束，提取但不包括约束名中的 null
                                String checkConstraint = extractCheckConstraint(idxStr);
                                if (checkConstraint != null && !checkConstraint.contains("`null`")) {
                                    checkConstraints.add(checkConstraint);
                                }
                            }
                        }
                    }
                }
            }
        } catch (Exception ignore) { }

        if (!tablePrimaryKeyCols.isEmpty()) {
            Set<String> pkSet = new LinkedHashSet<>();
            for (String c : tablePrimaryKeyCols) {
                pkSet.add(c.replace("`", ""));
                }
            String normTableKey = tableName.replace("`", "");
            tablePkColsMap.put(normTableKey, pkSet);
            }

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);
            if (i > 0) sb.append(",\n");

            String colName = cleanIdentifier(col.getColumnName());
            String colType = convertColumnType(col.getColDataType().getDataType(),
                    col.getColDataType().getArgumentsStringList());

            List<String> specs = getColumnSpecs(col);

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

            String colNameLower = col.getColumnName().replaceAll("[`'\"]", "").toLowerCase();
            if (!isPrimaryKey && tablePrimaryKeyCols.contains(colNameLower)) {
                isPrimaryKey = true;
            }

            if (columnNotNullMap.containsKey(colNameLower)) {
                isNotNull = true;
            }

            // 主键列统一使用 bigint 类型
            if (isPrimaryKey) {
                colType = "BIGINT";
            }

            sb.append("    ").append(colName).append(" ").append(colType);

            if (defaultValStr != null) {
                defaultValStr = defaultValStr.trim();
                if (defaultValStr.contains("SYSDATE") || defaultValStr.contains("CURRENT_TIMESTAMP")) {
                    sb.append(" DEFAULT NOW()");
                } else if (defaultValStr.equalsIgnoreCase("NULL")) {
                    sb.append(" DEFAULT NULL");
                } else if (colType.equalsIgnoreCase("VARCHAR(1)") &&
                        ("'Y'".equalsIgnoreCase(defaultValStr) || "'N'".equalsIgnoreCase(defaultValStr))) {
                    sb.append(" DEFAULT ").append("'Y'".equalsIgnoreCase(defaultValStr) ? "true" : "false");
                } else {
                    sb.append(" DEFAULT ").append(defaultValStr);
                }
            }

            if (isNotNull) {
                sb.append(" NOT NULL");
            }


            if (isPrimaryKey) {
                sb.append(" PRIMARY KEY");
            } else if (isUnique) {
                sb.append(" UNIQUE");
            }

            String columnCommentKey = tableName.replace("`", "") + "." + colName.replace("`", "");
            String columnComment = columnComments.get(columnCommentKey);

            if (columnComment != null && !columnComment.isEmpty()) {
                if ((columnComment.startsWith("'") && columnComment.endsWith("'")) ||
                        (columnComment.startsWith("\"") && columnComment.endsWith("\""))) {
                    columnComment = columnComment.substring(1, columnComment.length() - 1);
                }
                String escapedComment = columnComment.replace("'", "''");
                sb.append(" COMMENT '").append(escapedComment).append("'");
            }
        }

        addTableConstraints(createTable, tableName, tablePrimaryKeyCols, checkConstraints, sb);

        sb.append("\n)");

        String tableCommentKey = tableName.replace("`", "");
        String tableComment = tableComments.get(tableCommentKey);

        if (tableComment == null) {
            tableComment = extractTableComment(createTable);
        }

        if (tableComment != null && !tableComment.isEmpty()) {
            tableComment = tableComment.trim();
            if ((tableComment.startsWith("'") && tableComment.endsWith("'")) ||
                    (tableComment.startsWith("\"") && tableComment.endsWith("\""))) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            }
            String escapedComment = tableComment.replace("'", "''");
            sb.append(" ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_bin ROW_FORMAT=DYNAMIC COMMENT='")
                    .append(escapedComment).append("'");
        } else {
            sb.append(" ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_bin ROW_FORMAT=DYNAMIC");
            }

        sb.append(";\n\n");
        return sb.toString();
    }

    // 辅助方法：提取索引列
    private List<String> extractIndexColumns(CreateIndex createIndex) {
        List<String> columns = new ArrayList<>();
        try {
            List<?> colsObj = (List<?>)CreateIndex.class.getMethod("getColumns").invoke(createIndex);
        if (colsObj != null) {
            for (Object col : colsObj) {
                if (col instanceof Column) {
                    columns.add(cleanIdentifier(((Column) col).getColumnName()));
                } else if (col instanceof String) {
                    columns.add(cleanIdentifier((String) col));
                }
            }
        }
        } catch (Exception e) {
            String idxStr = createIndex.toString();
            int lpar = idxStr.indexOf('(');
            int rpar = idxStr.indexOf(')', lpar);
            if (lpar != -1 && rpar != -1) {
                String inParens = idxStr.substring(lpar + 1, rpar);
                String[] colArr = inParens.split(",");
                for (String raw : colArr) {
                    columns.add(cleanIdentifier(raw.trim()));
                }
            }
        }
        return columns;
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
                        addRawSql(sb.toString());
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
                        addRawSql(sb.toString());
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
                                .append(cleanIdentifier(getTableNameOnly(refTable)))
                                .append(" (")
                                .append(parseAndJoinCols(refCols))
                                .append(");\n\n");
                        addRawSql(sb.toString());
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
                        addRawSql(sb.toString());
                        continue;
                    }
                }
            }
        } else {
            String s = alter.toString();
            addRawSql(s + ";\n\n");
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
        StringBuilder sb = new StringBuilder();
        sb.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            sb.append("(");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                sb.append(colName);
                if (i < columns.size() - 1) sb.append(", ");
            }
            sb.append(")");
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

        sb.append(" VALUES").append(valuesPart).append(";\n\n");
        addRawSql(sb.toString());
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
        StringBuilder sb = new StringBuilder();
        sb.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = valueExpr.replace("SYSDATE", "NOW()");
            valueExpr = valueExpr.replace("CURRENT_TIMESTAMP", "NOW()");
            valueExpr = replaceBooleanLiteralsForGDB(valueExpr);
            sb.append(colName).append("=").append(valueExpr);
            if (i < cols.size() - 1) sb.append(", ");
        }
        sb.append(processWhereExpression(update.getWhere())).append(";\n\n");
        addRawSql(sb.toString());
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
        StringBuilder sb = new StringBuilder();
        sb.append("DELETE FROM ").append(tableName);
        sb.append(processWhereExpression(delete.getWhere())).append(";\n\n");
        addRawSql(sb.toString());
    }

    public String getGdbSql() {
        StringBuilder result = new StringBuilder();
        for (Chunk c : chunks) {
            if (c.type == ChunkType.CREATE_TABLE) {
                result.append(renderCreateTable(c.createTable));
            } else if (c.rawSql != null) {
                result.append(c.rawSql);
            }
        }
        return result.toString();
    }
}