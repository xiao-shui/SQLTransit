package org.example.SqlTransit.tool;

import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.statement.alter.Alter;
import net.sf.jsqlparser.statement.alter.AlterExpression;
import net.sf.jsqlparser.statement.comment.Comment;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.drop.Drop;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.update.Update;

import java.lang.reflect.Method;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Oracle -> PostgreSQL SQL 转换 Visitor
 *
 * 主要能力：
 * 1. 数据类型转换（Oracle 类型到 PostgreSQL 类型）
 * 2. CREATE TABLE 转换
 * 3. CREATE (UNIQUE) INDEX 转换
 * 4. DROP TABLE 转换
 * 5. INSERT / UPDATE / DELETE 基本语法转换
 * 6. COMMENT ON TABLE / COMMENT ON COLUMN 转换（保持单独写）
 */
public class OracleToPGVisitor extends StatementVisitorAdapter {
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
    private final StringBuilder pgSql = new StringBuilder();

    private void addRawSql(String sql) {
        if (sql != null && !sql.isEmpty()) {
            chunks.add(new Chunk(sql));
        }
    }

    /**
     * 清理标识符，去掉引号，转为小写（PostgreSQL 默认小写）
     */
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[\"`']+|[\"`']+$", "").toLowerCase(Locale.ROOT).trim();
    }

    /**
     * 处理表名字符串，去掉schema部分，返回小写表名
     */
    private String getTableNameOnly(String raw) {
        if (raw == null) return null;
        String s = raw.replaceAll("[\"`']", "");
        String[] parts = s.split("\\.");
        String tableName = parts.length > 0 ? parts[parts.length - 1] : s;
        return tableName.toLowerCase(Locale.ROOT).trim();
    }

    /**
     * 获取带 schema 的完整表名（如果存在 schema，则保留：schema.table），统一转为小写
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
        }
        return baseName;
    }

    /**
     * 去掉schema并清洗名称，返回小写索引名
     */
    private String cleanIdentifierNoSchema(String name) {
        if (name == null) return null;
        String cleaned = name.replaceAll("[\"`']", "");
        if (cleaned.contains(".")) {
            cleaned = cleaned.substring(cleaned.lastIndexOf(".") + 1);
        }
        cleaned = cleaned.trim().toLowerCase(Locale.ROOT);
        return cleaned;
    }

    /**
     * 列名参数全部小写（不加引号）
     */
    private String parseAndJoinCols(String cols) {
        if (cols == null) return "";
        String[] arr = cols.split(",");
        List<String> result = new ArrayList<>();
        for (String c : arr) {
            String clean = cleanIdentifier(c.trim());
            result.add(clean);
        }
        return String.join(", ", result);
    }

    /**
     * Oracle -> PostgreSQL 数据类型映射
     */
    private String convertDataType(String oracleType, List<String> args) {
        if (oracleType == null) return "VARCHAR(255)";
        String type = oracleType.toUpperCase(Locale.ROOT);
        
        switch (type) {
            case "NUMBER":
                if (args != null && args.size() == 2) {
                    // NUMBER(p,s)
                    try {
                        int scale = Integer.parseInt(args.get(1).trim());
                        if (scale == 0) {
                            // NUMBER(p,0) 根据精度转换为 INTEGER 或 BIGINT
                            int precision = Integer.parseInt(args.get(0).trim());
                            if (precision <= 9) {
                                return "INTEGER";
                            } else if (precision <= 18) {
                                return "BIGINT";
                            } else {
                                return "NUMERIC(" + args.get(0) + ",0)";
                            }
                        } else {
                            // NUMBER(p,s) 其中 s != 0，转为 NUMERIC
                            return "NUMERIC(" + args.get(0) + "," + args.get(1) + ")";
                        }
                    } catch (NumberFormatException e) {
                        return "NUMERIC(" + args.get(0) + "," + args.get(1) + ")";
                    }
                } else if (args != null && args.size() == 1) {
                    int precision = Integer.parseInt(args.get(0));
                    if (precision <= 9) {
                        return "INTEGER";
                    } else if (precision <= 18) {
                        return "BIGINT";
                    } else {
                        return "NUMERIC(" + args.get(0) + ")";
                    }
                }
                return "NUMERIC";
            case "VARCHAR2":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR(" + args.get(0) + ")";
                }
                return "VARCHAR(255)";
            case "NVARCHAR2":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR(" + args.get(0) + ")";
                }
                return "VARCHAR(255)";
            case "CHAR":
                if (args != null && !args.isEmpty()) {
                    return "CHAR(" + args.get(0) + ")";
                }
                return "CHAR(1)";
            case "NCHAR":
                if (args != null && !args.isEmpty()) {
                    return "CHAR(" + args.get(0) + ")";
                }
                return "CHAR(1)";
            case "DATE":
                return "TIMESTAMP";
            case "TIMESTAMP":
                return "TIMESTAMP";
            case "CLOB":
            case "NCLOB":
                return "TEXT";
            case "BLOB":
                return "BYTEA";
            case "RAW":
                if (args != null && !args.isEmpty()) {
                    return "BYTEA";
                }
                return "BYTEA";
            case "LONG":
                return "TEXT";
            case "FLOAT":
                return "DOUBLE PRECISION";
            case "BINARY_FLOAT":
                return "REAL";
            case "BINARY_DOUBLE":
                return "DOUBLE PRECISION";
            case "INTERVAL":
                return "INTERVAL";
            case "XMLTYPE":
                return "XML";
            default:
                if (args != null && !args.isEmpty()) {
                    return type + "(" + String.join(",", args) + ")";
                }
                return type;
        }
    }

    @Override
    public void visit(CreateTable createTable) {
        // 延迟渲染，先缓存 AST
        chunks.add(new Chunk(createTable));
    }

    /**
     * 渲染 CREATE TABLE（延迟执行）
     */
    private String renderCreateTable(CreateTable createTable) {
        StringBuilder sb = new StringBuilder();
        // 如果有 schema，则保留 schema.table 形式
        String tableName = getFullTableName(createTable.getTable());
        sb.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();
        boolean hasAnyColumnPk = false;

        if (columns != null) {
            for (int i = 0; i < columns.size(); i++) {
                ColumnDefinition col = columns.get(i);
                if (i > 0) sb.append(",\n");

                String colName = cleanIdentifier(col.getColumnName());
                String colType = convertDataType(
                        col.getColDataType().getDataType(),
                        col.getColDataType().getArgumentsStringList()
                );

                // 解析 column specs / 约束
                List<String> specs = new ArrayList<>();
                String fullColStr = col.toString();
                try {
                    Method m = ColumnDefinition.class.getMethod("getColumnSpecStrings");
                    Object result = m.invoke(col);
                    if (result instanceof List) {
                        for (Object o : (List<?>) result) {
                            if (o != null) specs.add(o.toString().trim());
                        }
                    }
                } catch (Exception e) {
                    String pattern = Pattern.quote(col.getColumnName()) + "\\s+.*?(?=,\\s*|$)";
                    Pattern r = Pattern.compile(pattern, Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                    Matcher mm = r.matcher(fullColStr);
                    if (mm.find()) {
                        String columnDef = mm.group();
                        String colNamePattern = Pattern.quote(col.getColumnName());
                        String dataTypePattern = Pattern.quote(col.getColDataType().getDataType());
                        String constraintsOnly = columnDef
                                .replaceFirst("^" + colNamePattern + "\\s+", "")
                                .replaceFirst("^" + dataTypePattern + "\\s*", "")
                                .trim();
                        specs = parseConstraintTokens(constraintsOnly);
                    }
                }
                
                // 如果 specs 为空或没有找到 DEFAULT，尝试直接从原始字符串中提取
                String extractedDefault = null;
                if (specs.isEmpty() || !specs.stream().anyMatch(s -> s.toUpperCase(Locale.ROOT).equals("DEFAULT"))) {
                    Pattern defaultPattern = Pattern.compile(
                            "(?i)DEFAULT\\s+([^\\s]+(?:\\s+[^\\s]+)*?)(?=\\s+(?:PRIMARY|UNIQUE|NOT|NULL|CHECK|,|$))",
                            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                    Matcher defaultMatcher = defaultPattern.matcher(fullColStr);
                    if (defaultMatcher.find()) {
                        extractedDefault = defaultMatcher.group(1).trim();
                    }
                }

                boolean isPrimaryKey = false;
                boolean isNotNull = false;
                boolean isUnique = false;
                String defaultVal = null;

                for (int j = 0; j < specs.size(); j++) {
                    String spec = specs.get(j);
                    String upper = spec.toUpperCase(Locale.ROOT);

                    if (j + 1 < specs.size()) {
                        String two = upper + " " + specs.get(j + 1).toUpperCase(Locale.ROOT);
                        if ("PRIMARY KEY".equals(two)) {
                            isPrimaryKey = true;
                            hasAnyColumnPk = true;
                            j++;
                            continue;
                        }
                        if ("NOT NULL".equals(two)) {
                            isNotNull = true;
                            j++;
                            continue;
                        }
                    }

                    if ("PRIMARY".equals(upper)) {
                        isPrimaryKey = true;
                        hasAnyColumnPk = true;
                    } else if ("NOT".equals(upper)) {
                        isNotNull = true;
                    } else if ("NULL".equals(upper)) {
                        // 单独的 NULL 忽略
                    } else if ("UNIQUE".equals(upper)) {
                        isUnique = true;
                    } else if ("DEFAULT".equals(upper)) {
                        // 合并 DEFAULT 后面的所有值，直到遇到下一个关键字
                        StringBuilder defaultBuilder = new StringBuilder();
                        int k = j + 1;
                        while (k < specs.size()) {
                            String nextSpec = specs.get(k);
                            String nextUpper = nextSpec.toUpperCase(Locale.ROOT);
                            // 如果遇到关键字，停止合并
                            if ("PRIMARY".equals(nextUpper) || "KEY".equals(nextUpper) || 
                                "NOT".equals(nextUpper) || "NULL".equals(nextUpper) ||
                                "UNIQUE".equals(nextUpper) || "CHECK".equals(nextUpper)) {
                                break;
                            }
                            if (defaultBuilder.length() > 0) {
                                defaultBuilder.append(" ");
                            }
                            defaultBuilder.append(nextSpec);
                            k++;
                        }
                        if (defaultBuilder.length() > 0) {
                            defaultVal = defaultBuilder.toString();
                            j = k - 1; // 跳过已处理的部分
                        }
                    }
                }

                // 兜底：如果通过 specs 未识别出 NOT NULL，但原始列定义字符串中包含 NOT NULL，则仍然标记为 NOT NULL
                if (!isNotNull && fullColStr != null) {
                    String upperColStr = fullColStr.toUpperCase(Locale.ROOT);
                    if (upperColStr.matches(".*\\bNOT\\s+NULL\\b.*")) {
                        isNotNull = true;
                    }
                }

                sb.append("    ").append(colName).append(" ").append(colType);

                // 默认值（优先使用从 specs 解析的，否则使用从原始字符串提取的）
                String finalDefaultVal = defaultVal != null ? defaultVal : extractedDefault;
                if (finalDefaultVal != null && !finalDefaultVal.isEmpty()) {
                    String dv = formatDefaultValue(finalDefaultVal.trim());
                    sb.append(" DEFAULT ").append(dv);
                }

                if (isPrimaryKey) {
                    sb.append(" PRIMARY KEY");
                } else {
                    if (isUnique) {
                        sb.append(" UNIQUE");
                    }
                    if (isNotNull) {
                        sb.append(" NOT NULL");
                    }
                }
            }
        }

        // 处理表级主键（从索引或原始 SQL 中解析）
        appendTablePrimaryKey(createTable, tableName, hasAnyColumnPk, sb);

        sb.append("\n);\n\n");
        return sb.toString();
    }

    /**
     * 如果未在列级定义主键，则从表级约束/索引中提取 PRIMARY KEY（保留约束名）
     */
    private void appendTablePrimaryKey(CreateTable createTable, String tableName, boolean hasColumnLevelPk, StringBuilder sb) {
        if (hasColumnLevelPk) {
            return;
        }

        List<String> pkCols = new ArrayList<>();
        String constraintName = null;

        // 1. 通过反射获取 CreateTable.getIndexes()
        try {
            Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
            List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
            if (indexes != null) {
                for (Object idx : indexes) {
                    String idxStr = idx.toString();
                    if (idxStr.toUpperCase(Locale.ROOT).contains("PRIMARY KEY")) {
                        // 约束名
                        try {
                            Method getNameMethod = idx.getClass().getMethod("getName");
                            Object nm = getNameMethod.invoke(idx);
                            if (nm != null) {
                                String nStr = cleanIdentifier(nm.toString());
                                if (!nStr.isEmpty()) constraintName = nStr;
                            }
                        } catch (Exception ignore) {
                        }
                        // 列名
                        try {
                            Method getColumnsMethod = idx.getClass().getMethod("getColumnsNames");
                            Object colsObj = getColumnsMethod.invoke(idx);
                            if (colsObj instanceof List) {
                                for (Object colObj : (List<?>) colsObj) {
                                    pkCols.add(cleanIdentifier(colObj.toString()));
                                }
                            }
                        } catch (Exception ignore) {
                        }
                        break;
                    }
                }
            }
        } catch (Exception ignore) {
        }

        // 2. 如果上面没拿到，则从原始 SQL 字符串中用正则解析
        if (pkCols.isEmpty()) {
            String createStr = createTable.toString();
            Pattern pkPattern = Pattern.compile(
                    "CONSTRAINT\\s+([^\\s]+)\\s+PRIMARY\\s+KEY\\s*\\(([^)]+)\\)",
                    Pattern.CASE_INSENSITIVE);
            Matcher m = pkPattern.matcher(createStr);
            if (m.find()) {
                constraintName = cleanIdentifier(m.group(1));
                String cols = m.group(2);
                String[] colArr = cols.split(",");
                for (String c : colArr) {
                    pkCols.add(cleanIdentifier(c.trim()));
                }
            } else {
                // 退一步，直接找 PRIMARY KEY (...)
                Pattern pkPattern2 = Pattern.compile(
                        "PRIMARY\\s+KEY\\s*\\(([^)]+)\\)",
                        Pattern.CASE_INSENSITIVE);
                Matcher m2 = pkPattern2.matcher(createStr);
                if (m2.find()) {
                    String cols = m2.group(1);
                    String[] colArr = cols.split(",");
                    for (String c : colArr) {
                        pkCols.add(cleanIdentifier(c.trim()));
                    }
                }
            }
        }

        if (!pkCols.isEmpty()) {
            if (constraintName != null && !constraintName.isEmpty()) {
                sb.append(",\n    CONSTRAINT ").append(constraintName).append(" PRIMARY KEY (");
            } else {
                sb.append(",\n    PRIMARY KEY (");
            }
            for (int i = 0; i < pkCols.size(); i++) {
                if (i > 0) sb.append(", ");
                sb.append(pkCols.get(i));
            }
            sb.append(")");
        }
    }

    // ----------------- COMMENT -----------------

    @Override
    public void visit(Comment comment) {
        // Oracle 和 PostgreSQL 都使用 COMMENT ON TABLE/COLUMN，直接转换
        String commentStr = comment.toString();
        
        // 处理表注释
        Pattern tablePattern = Pattern.compile(
                "^\\s*COMMENT\\s+ON\\s+TABLE\\s+([^\\s]+)\\s+IS\\s+(['\"])(.*?)\\2",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher tableMatcher = tablePattern.matcher(commentStr);
        if (tableMatcher.find()) {
            String table = tableMatcher.group(1);
            String commentTxt = tableMatcher.group(3);
            
            // 清理表名（去掉schema，转为小写）
            String tableName = getTableNameOnly(table);

            StringBuilder sb = new StringBuilder();
            sb.append("COMMENT ON TABLE ").append(tableName).append(" IS ");
            sb.append("'").append(escapeComment(commentTxt)).append("';\n");
            addRawSql(sb.toString());
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
                columnName = cleanIdentifier(columnName);

                StringBuilder sb = new StringBuilder();
                sb.append("COMMENT ON COLUMN ").append(tableName)
                        .append(".").append(columnName).append(" IS ");
                sb.append("'").append(escapeComment(commentTxt)).append("';\n");
                addRawSql(sb.toString());
            }
            return;
        }

        // 其他注释格式，直接输出
        addRawSql(commentStr + ";\n\n");
    }

    // ----------------- CREATE INDEX -----------------

    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = cleanIdentifierNoSchema(createIndex.getIndex().getName());

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
            if (result instanceof Boolean) isUnique = (Boolean) result;
        } catch (Exception e) {
            String text = createIndex.toString().toUpperCase(Locale.ROOT);
            if (text.contains("UNIQUE") || (indexName != null && indexName.toUpperCase(Locale.ROOT).contains("UNIQUE"))) {
                isUnique = true;
            }
        }

        List<String> columns = extractIndexColumns(createIndex);

        StringBuilder sb = new StringBuilder();
        sb.append("CREATE");
        if (isUnique) sb.append(" UNIQUE");
        sb.append(" INDEX ").append(indexName)
                .append(" ON ").append(tableName)
                .append(" (").append(String.join(", ", columns)).append(");\n\n");
        addRawSql(sb.toString());
    }

    /**
     * 辅助方法：提取索引列
     */
    private List<String> extractIndexColumns(CreateIndex createIndex) {
        List<String> columns = new ArrayList<>();
        try {
            Method getColumnsMethod = CreateIndex.class.getMethod("getColumns");
            List<?> colsObj = (List<?>) getColumnsMethod.invoke(createIndex);
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
                    String clean = cleanIdentifier(raw.trim());
                    if (!clean.isEmpty()) columns.add(clean);
                }
            }
        }
        return columns;
    }

    // ----------------- ALTER -----------------

    @Override
    public void visit(Alter alter) {
        String tableName = null;
        try {
            Method getTableMethod = Alter.class.getMethod("getTable");
            Object tblObj = getTableMethod.invoke(alter);
            if (tblObj != null && tblObj.getClass().getMethod("getName") != null) {
                Table tableObj = (Table) tblObj;
                if (tableObj.getSchemaName() != null && !tableObj.getSchemaName().isEmpty()) {
                    tableName = cleanIdentifier(tableObj.getSchemaName()) + "." + cleanIdentifier(tableObj.getName());
                } else {
                    tableName = cleanIdentifier(tableObj.getName());
                }
            }
        } catch (Exception e) {
            String alterStr = alter.toString();
            Pattern p = Pattern.compile("ALTER TABLE\\s+((\"[^\"]+\"\\.)?\"[^\"]+\"|`[^`]+`|[\\w]+)", Pattern.CASE_INSENSITIVE);
            Matcher m = p.matcher(alterStr);
            if (m.find()) {
                String t = m.group(1);
                t = t.replaceAll("[`'\"]+", "");
                tableName = cleanIdentifier(t);
            }
        }
        if (tableName == null) {
            tableName = "unknown_table";
        }

        List<AlterExpression> expressions = null;
        try {
            Method getAlterExprMethod = Alter.class.getMethod("getAlterExpressions");
            Object alterExprsObj = getAlterExprMethod.invoke(alter);
            if (alterExprsObj instanceof List) {
                @SuppressWarnings("unchecked")
                List<AlterExpression> alterExprs = (List<AlterExpression>) alterExprsObj;
                expressions = alterExprs;
            }
        } catch (Exception ignore) {
        }

        if (expressions != null) {
            for (AlterExpression expr : expressions) {
                if (expr == null) continue;
                String opStr = expr.getOperation() != null ? expr.getOperation().toString().toUpperCase(Locale.ROOT) : "";

                // 处理 ADD CONSTRAINT PRIMARY KEY / UNIQUE / FOREIGN KEY / CHECK
                if ("ADD".equals(opStr) && expr.getIndex() != null) {
                    Object idx = expr.getIndex();
                    String idxStr = idx.toString();
                    StringBuilder sb = new StringBuilder();

                    Pattern pkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*PRIMARY KEY\\s*\\(([^)]+)\\)",
                            Pattern.CASE_INSENSITIVE);
                    Matcher pkMatcher = pkPattern.matcher(idxStr);
                    if (pkMatcher.find()) {
                        String cols = pkMatcher.group(2);
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD PRIMARY KEY (")
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
                        String cols = uqMatcher.group(2);
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD UNIQUE (")
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
                        String localCols = fkMatcher.group(2);
                        String refTable = fkMatcher.group(3);
                        String refCols = fkMatcher.group(4);
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD FOREIGN KEY (")
                                .append(parseAndJoinCols(localCols))
                                .append(") REFERENCES ")
                                .append(cleanIdentifier(refTable.replaceAll("[`'\"]", "")))
                                .append(" (")
                                .append(parseAndJoinCols(refCols))
                                .append(");\n\n");
                        addRawSql(sb.toString());
                        continue;
                    }

                    Pattern checkPattern = Pattern.compile(
                            "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*CHECK\\s*\\((.+)\\)",
                            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                    Matcher checkMatcher = checkPattern.matcher(idxStr);
                    if (checkMatcher.find()) {
                        String checkExpr = checkMatcher.group(2).trim();
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD CHECK (").append(checkExpr).append(");\n\n");
                        addRawSql(sb.toString());
                        continue;
                    }
                }
            }
        } else {
            // 无法解析时直接输出
            String s = alter.toString();
            addRawSql(s + ";\n\n");
        }
    }

    // ----------------- DROP TABLE -----------------

    @Override
    public void visit(Drop drop) {
        String type = drop.getType();
        if (type == null || !"TABLE".equalsIgnoreCase(type)) {
            addRawSql(drop.toString() + ";\n\n");
            return;
        }

        String tableName;
        if (drop.getName() != null) {
            tableName = cleanIdentifier(drop.getName().getName());
        } else {
            tableName = drop.toString().replaceAll("(?i)DROP\\s+TABLE\\s+(IF\\s+EXISTS\\s+)?", "").trim();
            tableName = cleanIdentifier(tableName);
        }

        addRawSql("DROP TABLE IF EXISTS " + tableName + ";\n\n");
    }

    // ----------------- INSERT / UPDATE / DELETE -----------------

    @Override
    public void visit(Insert insert) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(insert.getTable().getName());
        sb.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            sb.append(" (");
            for (int i = 0; i < columns.size(); i++) {
                sb.append(cleanIdentifier(columns.get(i).getColumnName()));
                if (i < columns.size() - 1) sb.append(", ");
            }
            sb.append(")");
        }

        String valuesStr = insert.toString();
        int idx = valuesStr.toUpperCase(Locale.ROOT).indexOf("VALUES");
        String valuesPart = "";
        if (idx != -1) {
            valuesPart = valuesStr.substring(idx + 6);
            valuesPart = convertOracleFunctions(valuesPart);
        }

        sb.append(" VALUES").append(valuesPart).append(";\n\n");
        addRawSql(sb.toString());
    }

    @Override
    public void visit(Update update) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(update.getTable().getName());
        sb.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        @SuppressWarnings("unchecked")
        List<Expression> exprs = (List<Expression>) (List<?>) update.getExpressions();

        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = convertOracleFunctions(valueExpr);
            sb.append(colName).append(" = ").append(valueExpr);
            if (i < cols.size() - 1) sb.append(", ");
        }

        Expression where = update.getWhere();
        if (where != null) {
            sb.append(" WHERE ").append(convertOracleFunctions(where.toString()));
        }

        sb.append(";\n\n");
        addRawSql(sb.toString());
    }

    @Override
    public void visit(Delete delete) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(delete.getTable().getName());
        sb.append("DELETE FROM ").append(tableName);

        Expression where = delete.getWhere();
        if (where != null) {
            sb.append(" WHERE ").append(convertOracleFunctions(where.toString()));
        }

        sb.append(";\n\n");
        addRawSql(sb.toString());
    }

    /**
     * 将 Oracle 表达式中常见函数/语法转换为 PostgreSQL 风格
     */
    private String convertOracleFunctions(String sql) {
        if (sql == null) return "";
        String result = sql;
        // SYSDATE -> CURRENT_TIMESTAMP
        result = result.replaceAll("(?i)\\bSYSDATE\\b", "CURRENT_TIMESTAMP");
        // TO_DATE -> TO_TIMESTAMP
        result = result.replaceAll("(?i)\\bTO_DATE\\s*\\(", "TO_TIMESTAMP(");
        // NVL -> COALESCE
        result = result.replaceAll("(?i)\\bNVL\\s*\\(", "COALESCE(");
        // 标识符双引号保持（PostgreSQL 使用双引号）
        // 去掉反引号，转为双引号
        result = result.replace("`", "\"");
        return result;
    }

    /**
     * 格式化默认值为 PostgreSQL 格式
     * - 函数调用（如 CURRENT_TIMESTAMP）不加引号
     * - 数字值不加引号
     * - 字符串值如果已有引号则保持，否则加单引号
     * - NULL 不加引号
     */
    private String formatDefaultValue(String defaultValue) {
        if (defaultValue == null || defaultValue.isEmpty()) {
            return "";
        }
        
        // 先转换Oracle函数
        String converted = convertOracleFunctions(defaultValue);
        String trimmed = converted.trim();
        
        // NULL值
        if ("NULL".equalsIgnoreCase(trimmed)) {
            return "NULL";
        }
        
        // 函数调用（如 CURRENT_TIMESTAMP, NOW(), TO_TIMESTAMP(...) 等）
        String upperTrimmed = trimmed.toUpperCase(Locale.ROOT);
        if (upperTrimmed.startsWith("CURRENT_TIMESTAMP") ||
            upperTrimmed.startsWith("CURRENT_DATE") ||
            upperTrimmed.startsWith("CURRENT_TIME") ||
            upperTrimmed.startsWith("NOW()") ||
            upperTrimmed.startsWith("TO_TIMESTAMP(") ||
            upperTrimmed.startsWith("COALESCE(") ||
            upperTrimmed.contains("(")) {
            return trimmed;
        }
        
        // 布尔值
        if ("TRUE".equalsIgnoreCase(trimmed) || "FALSE".equalsIgnoreCase(trimmed)) {
            return trimmed.toUpperCase(Locale.ROOT);
        }
        
        // 如果已经有引号（单引号或双引号），保持原样（但将双引号转为单引号）
        if ((trimmed.startsWith("'") && trimmed.endsWith("'")) ||
            (trimmed.startsWith("\"") && trimmed.endsWith("\""))) {
            // 将双引号转为单引号
            if (trimmed.startsWith("\"")) {
                return "'" + trimmed.substring(1, trimmed.length() - 1).replace("'", "''") + "'";
            }
            return trimmed; // 已经是单引号，保持原样
        }
        
        // 数字值（整数或小数）
        try {
            Double.parseDouble(trimmed);
            return trimmed; // 数字不加引号
        } catch (NumberFormatException e) {
            // 不是数字，当作字符串处理，加单引号并转义内部单引号
            return "'" + trimmed.replace("'", "''") + "'";
        }
    }

    // ----------------- 约束解析辅助 -----------------

    /** 智能拆分约束 token */
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

    private String escapeComment(String comment) {
        if (comment == null) return "";
        // 转义单引号
        return comment.replace("'", "''");
    }

    // ----------------- 输出结果 -----------------

    public String getPostgresqlSql() {
        // 按照chunks的顺序输出，保持原始语句顺序
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

    public void clear() {
        pgSql.setLength(0);
        chunks.clear();
    }
}
