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

public class MysqlToOracleVisitor extends StatementVisitorAdapter {
    private final StringBuilder oracleSql = new StringBuilder();
    private final List<String> comments = new ArrayList<>(); // 用于保存要输出的COMMENT ON语句

    // 工具方法：清理标识符（去除引号并大写）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
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

    // 工具方法：处理 WHERE 条件表达式
    private String processWhereExpression(Expression where) {
        if (where == null) return "";
        String expr = where.toString();
        expr = expr.replace("CURRENT_TIMESTAMP", "SYSDATE");
        expr = replaceBooleanLiterals(expr);
        expr = uppercaseWhereColumnNames(expr);
        return " WHERE " + expr;
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

    // 处理 CREATE TABLE
    @Override
    public void visit(CreateTable createTable) {
        String tableName = cleanIdentifier(createTable.getTable().getName());
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
                String fullColStr = col.toString();

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

            // 构建字段定义
            oracleSql.append("    ").append(colName).append(" ").append(colType);

            if (isAutoIncrement) {
                oracleSql.append(" GENERATED BY DEFAULT AS IDENTITY");
            }

            if (defaultValStr != null) {
                // 处理特殊默认值
                defaultValStr = defaultValStr.trim();
                if (defaultValStr.contains("CURRENT_TIMESTAMP")) {
                    oracleSql.append(" DEFAULT SYSDATE");
                } else if (colType.equalsIgnoreCase("VARCHAR2(1)") &&
                        (defaultValStr.equalsIgnoreCase("true") || defaultValStr.equalsIgnoreCase("false"))) {
                    oracleSql.append(" DEFAULT '").append(defaultValStr.equalsIgnoreCase("true") ? "Y" : "N").append("'");
                } else if (defaultValStr.startsWith("'") && defaultValStr.endsWith("'")) {
                    // 带引号的字符串
                    oracleSql.append(" DEFAULT ").append(defaultValStr);
                } else {
                    // 数字或其他值
                    oracleSql.append(" DEFAULT ").append(defaultValStr);
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


    // 处理 CREATE INDEX
    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = cleanIdentifier(createIndex.getIndex().getName());
        String tableName = cleanIdentifier(createIndex.getTable().getName());
        boolean isUnique = createIndex.toString().toUpperCase().contains("UNIQUE") ||
                (indexName != null && indexName.startsWith("UNIQUE_"));

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
                    if (!clean.isEmpty()) columns.add(clean.toUpperCase());
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

    // 处理 INSERT
    @Override
    public void visit(Insert insert) {
        String tableName = cleanIdentifier(insert.getTable().getName());
        oracleSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            oracleSql.append("(");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                oracleSql.append(colName);
                if (i < columns.size() - 1) oracleSql.append(", ");
            }
            oracleSql.append(")");
        }

        String valuesStr = insert.toString().toUpperCase();
        int valuesIdx = valuesStr.indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = insert.toString().substring(valuesIdx + 6);
            valuesPart = valuesPart.replace("CURRENT_TIMESTAMP", "SYSDATE");
            valuesPart = replaceBooleanLiterals(valuesPart);
        }

        oracleSql.append(" VALUES").append(valuesPart).append(";\n\n");
    }

    // 处理 UPDATE
    @Override
    public void visit(Update update) {
        String tableName = cleanIdentifier(update.getTable().getName());
        oracleSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = valueExpr.replace("CURRENT_TIMESTAMP", "SYSDATE");
            valueExpr = replaceBooleanLiterals(valueExpr);
            valueExpr = uppercaseWhereColumnNames(valueExpr);
            oracleSql.append(colName).append("=").append(valueExpr);
            if (i < cols.size() - 1) oracleSql.append(", ");
        }

        oracleSql.append(processWhereExpression(update.getWhere())).append(";\n\n");
    }

    // 处理 DELETE
    @Override
    public void visit(Delete delete) {
        String tableName = cleanIdentifier(delete.getTable().getName());
        oracleSql.append("DELETE FROM ").append(tableName);
        oracleSql.append(processWhereExpression(delete.getWhere())).append(";\n\n");
    }

    // 获取最终 Oracle SQL
    public String getOracleSql() {
        return oracleSql.toString();
    }
}
