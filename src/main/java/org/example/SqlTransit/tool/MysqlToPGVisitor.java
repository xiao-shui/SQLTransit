package org.example.SqlTransit.tool;

import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.table.Index;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.drop.Drop;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.statement.alter.Alter;
import net.sf.jsqlparser.statement.alter.AlterExpression;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;

import java.lang.reflect.Method;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MysqlToPGVisitor extends StatementVisitorAdapter {
    private final StringBuilder postgresqlSql = new StringBuilder();
    private final List<String> comments = new ArrayList<>(); // 用于保存要输出的COMMENT ON语句

    // 工具方法：清理标识符（去掉首尾引号，转为小写，但保留中间的点号用于schema.table）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[`'\"]+|[`'\"]+$", "").toLowerCase();
    }

    /**
     * 获取带模式名的完整表名（如果存在 schema，则保留：schema.table），并统一转为小写
     */
    private String getFullTableName(Table table) {
        if (table == null) return null;
        String baseName = cleanIdentifier(table.getName());
        try {
            String schema = table.getSchemaName();
            if (schema != null && !schema.isEmpty()) {
                return cleanIdentifier(schema) + "." + baseName;
            }
        } catch (Exception ignore) {
            // 某些版本的 JSqlParser 可能不存在 getSchemaName 方法
        }
        return baseName;
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

    @Override
    public void visit(Drop drop) {
        // 只关心 DROP TABLE，其它类型直接输出
        String type = drop.getType();
        if (type == null || !"TABLE".equalsIgnoreCase(type)) {
            postgresqlSql.append(drop.toString()).append(";\n\n");
            return;
        }

        String tableName;
        if (drop.getName() != null) {
            Table t = drop.getName();
            tableName = getFullTableName(t);
        } else {
            String raw = drop.toString().replaceAll("(?i)DROP\\s+TABLE\\s+(IF\\s+EXISTS\\s+)?", "").trim();
            // 保留 schema 前缀，仅移除首尾引号并转为小写
            raw = raw.replaceAll("^[`'\"]+|[`'\"]+$", "");
            tableName = raw.toLowerCase(Locale.ROOT);
        }

        postgresqlSql.append("DROP TABLE IF EXISTS ").append(tableName).append(";\n");
    }

    // 处理 CREATE TABLE
    @Override
    public void visit(CreateTable createTable) {
        String tableName = getFullTableName(createTable.getTable());
        postgresqlSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();
        boolean hasColumnLevelPrimaryKey = false;

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
                hasColumnLevelPrimaryKey = true;
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

        // 追加表级主键（如果列级未定义）
        appendTablePrimaryKey(createTable, tableName, hasColumnLevelPrimaryKey);

        // 表级约束处理（外键、检查约束等）
        processTableLevelConstraints(createTable, tableName);

        postgresqlSql.append("\n);\n\n");

        // 表级索引处理（普通 KEY / UNIQUE KEY，排除 PRIMARY KEY）
        processTableIndexes(createTable, tableName);

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

    /**
     * 如果未在列级定义主键，则尝试从表级索引提取主键并追加
     */
    private void appendTablePrimaryKey(CreateTable createTable, String tableName, boolean hasColumnLevelPrimaryKey) {
        if (hasColumnLevelPrimaryKey) {
            return;
        }

        List<String> tablePrimaryKeyCols = new ArrayList<>();

        // 优先使用反射获取索引列表
        try {
            java.lang.reflect.Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<Index> indexes = (List<Index>) getIndexesMethod.invoke(createTable);
            if (indexes != null) {
                for (Index idx : indexes) {
                    String idxStr = idx.toString();
                    // 移除 USING BTREE 等后缀
                    idxStr = idxStr.replaceAll("(?i)\\s+USING\\s+\\w+", "");
                    if (idxStr.toUpperCase().contains("PRIMARY KEY")) {
                        for (Object colObj : idx.getColumnsNames()) {
                            tablePrimaryKeyCols.add(cleanIdentifier(colObj.toString()));
                        }
                        break;
                    }
                }
            }
        } catch (Exception e) {
            // 回退到正则解析
            String createStr = createTable.toString();
            // 移除 USING BTREE 等后缀
            createStr = createStr.replaceAll("(?i)\\s+USING\\s+\\w+", "");
            Pattern pkPattern = Pattern.compile("PRIMARY KEY\\s*\\(([^)]+)\\)", Pattern.CASE_INSENSITIVE);
            Matcher m = pkPattern.matcher(createStr);
            if (m.find()) {
                String cols = m.group(1);
                String[] colArr = cols.split(",");
                for (String col : colArr) {
                    tablePrimaryKeyCols.add(cleanIdentifier(col.trim()));
                }
            }
        }

        if (!tablePrimaryKeyCols.isEmpty()) {
            postgresqlSql.append(",\n    PRIMARY KEY (")
                    .append(String.join(", ", tablePrimaryKeyCols))
                    .append(")");
        }
    }

    /**
     * 处理表级约束（外键、检查约束、唯一约束等）
     */
    private void processTableLevelConstraints(CreateTable createTable, String tableName) {
        String createStr = createTable.toString();
        // 移除 USING BTREE 等后缀
        createStr = createStr.replaceAll("(?i)\\s+USING\\s+\\w+", "");

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

            postgresqlSql.append(",\n    CONSTRAINT ").append(constraintName)
                    .append(" FOREIGN KEY (").append(parseAndJoinCols(columns)).append(")")
                    .append(" REFERENCES ").append(refTable)
                    .append(" (").append(parseAndJoinCols(refColumns)).append(")");
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

            postgresqlSql.append(",\n    CONSTRAINT ").append(constraintName)
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

            postgresqlSql.append(",\n    CONSTRAINT ").append(constraintName)
                    .append(" UNIQUE (").append(parseAndJoinCols(columns)).append(")");
        }
    }

    /**
     * 处理表级索引（KEY / UNIQUE KEY），生成独立的 CREATE INDEX 语句
     * 例如：
     *   KEY `agi_project_file_permission_project_id_INDEX` (`project_id`) USING BTREE
     * 转换为：
     *   CREATE INDEX agi_project_file_permission_project_id_index ON schema.table_name (project_id);
     */
    @SuppressWarnings("unchecked")
    private void processTableIndexes(CreateTable createTable, String tableName) {
        try {
            Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<Index> indexes = (List<Index>) getIndexesMethod.invoke(createTable);
            if (indexes == null || indexes.isEmpty()) {
                return;
            }

            for (Index idx : indexes) {
                if (idx == null) continue;

                String idxStr = idx.toString();
                String idxStrUpper = idxStr.toUpperCase(Locale.ROOT);

                // 跳过包含 PRIMARY KEY 的索引（已在主键处理中处理）
                if (idxStrUpper.contains("PRIMARY KEY")) {
                    continue;
                }

                // 判断是否唯一索引
                boolean isUnique = idxStrUpper.contains("UNIQUE");

                // 索引名
                String indexName = null;
                try {
                    if (idx.getName() != null) {
                        indexName = cleanIdentifier(idx.getName());
                    }
                } catch (Exception ignore) {
                }
                if (indexName == null || indexName.isEmpty()) {
                    // 尝试从字符串解析
                    Pattern namePattern = Pattern.compile(
                            "(?i)(?:UNIQUE\\s+)?KEY\\s+([^\\s(]+)",
                            Pattern.CASE_INSENSITIVE);
                    Matcher m = namePattern.matcher(idxStr);
                    if (m.find()) {
                        indexName = cleanIdentifier(m.group(1));
                    }
                }
                if (indexName == null || indexName.isEmpty()) {
                    // 仍然没有索引名时，生成一个
                    indexName = "idx_" + tableName.replace('.', '_');
                }

                // 列名
                List<String> idxColumns = new ArrayList<>();
                try {
                    List<String> cols = idx.getColumnsNames();
                    if (cols != null) {
                        for (Object colObj : cols) {
                            if (colObj != null) {
                                idxColumns.add(cleanIdentifier(colObj.toString()));
                            }
                        }
                    }
                } catch (Exception ignore) {
                }

                // 如果通过 API 未取到列名，则退回到字符串解析
                if (idxColumns.isEmpty()) {
                    Pattern colsPattern = Pattern.compile("\\(([^)]+)\\)");
                    Matcher m = colsPattern.matcher(idxStr);
                    if (m.find()) {
                        String cols = m.group(1);
                        String[] colArr = cols.split(",");
                        for (String c : colArr) {
                            String cn = c.trim().replaceAll("[`'\"]", "");
                            if (!cn.isEmpty()) {
                                idxColumns.add(cleanIdentifier(cn));
                            }
                        }
                    }
                }

                if (idxColumns.isEmpty()) {
                    continue;
                }

                // 生成 CREATE INDEX 语句（移除 USING BTREE 等存储选项）
                postgresqlSql.append("CREATE");
                if (isUnique) {
                    postgresqlSql.append(" UNIQUE");
                }
                postgresqlSql.append(" INDEX ").append(indexName)
                        .append(" ON ").append(tableName)
                        .append(" (").append(String.join(", ", idxColumns)).append(");\n\n");
            }
        } catch (Exception ignore) {
            // 反射失败时忽略，不影响主流程
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

        List<String> columns = new ArrayList<>();
        List<?> colsObj = null;
        try {
            colsObj = (List<?>) CreateIndex.class.getMethod("getColumns").invoke(createIndex);
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

        postgresqlSql.append("CREATE");
        if (isUnique) postgresqlSql.append(" UNIQUE");
        postgresqlSql.append(" INDEX ").append(indexName)
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
                Table tableObj = (Table) tblObj;
                if (tableObj.getSchemaName() != null && !tableObj.getSchemaName().isEmpty()) {
                    tableName = cleanIdentifier(tableObj.getSchemaName()) + "." + cleanIdentifier(tableObj.getName());
                } else {
                    tableName = getFullTableName(tableObj);
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
            tableName = "unknown_table";
        }

        // 优先尝试通过 AlterExpression 解析
        List<AlterExpression> expressions = null;
        try {
            Method getAlterExprMethod = Alter.class.getMethod("getAlterExpressions");
            Object alterExprsObj = getAlterExprMethod.invoke(alter);
            if (alterExprsObj instanceof List) {
                @SuppressWarnings("unchecked")
                List<AlterExpression> alterExprs = (List<AlterExpression>) alterExprsObj;
                expressions = alterExprs;
            }
        } catch (Exception e) {
            // ignore
        }

        if (expressions != null) {
            for (AlterExpression expr : expressions) {
                if (expr == null) continue;
                String opStr = expr.getOperation() != null ? expr.getOperation().toString().toUpperCase() : "";
                if ("ADD".equals(opStr) && expr.getIndex() != null) {
                    Object idx = expr.getIndex();
                    String idxStr = idx.toString();
                    StringBuilder sb = new StringBuilder();

                    // PRIMARY KEY 约束
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
                        postgresqlSql.append(sb.toString());
                        continue;
                    }

                    // UNIQUE 约束
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
                        postgresqlSql.append(sb.toString());
                        continue;
                    }

                    // FOREIGN KEY 约束
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
                        postgresqlSql.append(sb.toString());
                        continue;
                    }

                    // CHECK 约束
                    Pattern checkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*CHECK\\s*\\((.+)\\)",
                            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
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
                        postgresqlSql.append(sb.toString());
                        continue;
                    }
                }
            }
        } else {
            postgresqlSql.append(alterStr).append(";\n\n");
        }

        // 如果 AlterExpression 解析失败或为空，直接从字符串解析常见形式
        if (expressions == null || expressions.isEmpty()) {
            // ADD CONSTRAINT PRIMARY KEY
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
                postgresqlSql.append(sb.toString());
                return;
            }

            // ADD CONSTRAINT UNIQUE
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
                postgresqlSql.append(sb.toString());
                return;
            }

            // ADD INDEX → CREATE INDEX
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
                postgresqlSql.append(sb.toString());
                return;
            }

            // ADD CONSTRAINT FOREIGN KEY
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
                postgresqlSql.append(sb.toString());
                return;
            }

            // ADD CONSTRAINT CHECK
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
                postgresqlSql.append(sb.toString());
                return;
            }
        }

        // 如果无法识别具体结构，则直接输出原始 ALTER 语句
        postgresqlSql.append(alterStr).append(";\n\n");
    }

    // 处理 INSERT
    @Override
    public void visit(Insert insert) {
        String tableName = getFullTableName(insert.getTable());
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
        String tableName = getFullTableName(update.getTable());
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
        String tableName = getFullTableName(delete.getTable());
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