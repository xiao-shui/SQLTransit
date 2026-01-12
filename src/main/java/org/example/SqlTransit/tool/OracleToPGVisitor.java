package org.example.SqlTransit.tool;

import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.expression.Function;
import net.sf.jsqlparser.expression.StringValue;
import net.sf.jsqlparser.expression.DoubleValue;
import net.sf.jsqlparser.expression.DateValue;
import net.sf.jsqlparser.expression.LongValue;
import net.sf.jsqlparser.expression.operators.relational.ExpressionList;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.schema.Table;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.statement.select.Select;
import net.sf.jsqlparser.statement.select.PlainSelect;
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
        String sql = convertInsert(insert);
        addRawSql(sql);
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
                if (i < columns.size() - 1) sb.append(", ");
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

    @Override
    public void visit(Update update) {
        String sql = convertUpdate(update);
        addRawSql(sql);
    }

    private String convertUpdate(Update update) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(update.getTable().getName());
        sb.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        @SuppressWarnings("unchecked")
        List<Expression> exprs = (List<Expression>) (List<?>) update.getExpressions();

        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            Expression expression = exprs.get(i);
            sb.append(colName).append(" = ");
            sb.append(convertExpression(expression));
            if (i < cols.size() - 1) {
                sb.append(", ");
            }
        }

        Expression where = update.getWhere();
        if (where != null) {
            sb.append(" WHERE ").append(convertExpression(where));
        }

        return sb.append(";\n\n").toString();
    }

    @Override
    public void visit(Delete delete) {
        String sql = convertDelete(delete);
        addRawSql(sql);
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

    @Override
    @SuppressWarnings("deprecation")
    public void visit(Select select) {
        String sql = convertSelect(select);
        addRawSql(sql);
    }

    private String convertSelect(Select select) {
        StringBuilder sb = new StringBuilder();
        
        if (select.getSelectBody() instanceof PlainSelect) {
            PlainSelect plainSelect = (PlainSelect) select.getSelectBody();
            
            // 处理 SELECT 列表
            sb.append("SELECT ");
            if (plainSelect.getSelectItems() != null) {
                boolean first = true;
                for (Object item : plainSelect.getSelectItems()) {
                    if (!first) sb.append(", ");
                    String itemStr = item.toString();
                    itemStr = convertOracleFunctions(itemStr);
                    sb.append(itemStr);
                    first = false;
                }
            } else {
                sb.append("*");
            }
            
            // 处理 FROM
            if (plainSelect.getFromItem() != null) {
                String fromStr = plainSelect.getFromItem().toString();
                // 转换表名，保留 schema
                if (plainSelect.getFromItem() instanceof Table) {
                    Table table = (Table) plainSelect.getFromItem();
                    fromStr = getFullTableName(table);
                } else {
                    fromStr = convertOracleFunctions(fromStr);
                }
                sb.append(" FROM ").append(fromStr);
            }
            
            // 处理 WHERE
            if (plainSelect.getWhere() != null) {
                String whereStr = convertExpression(plainSelect.getWhere());
                sb.append(" WHERE ").append(whereStr);
            }
            
            // 处理 ORDER BY
            if (plainSelect.getOrderByElements() != null) {
                sb.append(" ORDER BY ");
                boolean first = true;
                for (Object orderElem : plainSelect.getOrderByElements()) {
                    if (!first) sb.append(", ");
                    String orderStr = orderElem.toString();
                    orderStr = convertOracleFunctions(orderStr);
                    sb.append(orderStr);
                    first = false;
                }
            }
            
            // 处理 Oracle 分页（FETCH FIRST ... ROWS ONLY 或 OFFSET ... ROWS FETCH NEXT ... ROWS ONLY）
            // Oracle 使用 getFetch() 和 getOffset() 而不是 getLimit()
            long offset = 0;
            long rowCount = 0;
            
            // 获取 OFFSET（如果存在）
            try {
                Method getOffsetMethod = PlainSelect.class.getMethod("getOffset");
                Object offsetObj = getOffsetMethod.invoke(plainSelect);
                if (offsetObj != null) {
                    // Offset 对象有 getOffset() 方法返回 LongValue
                    try {
                        Method getOffsetValueMethod = offsetObj.getClass().getMethod("getOffset");
                        Object offsetValue = getOffsetValueMethod.invoke(offsetObj);
                        if (offsetValue instanceof LongValue) {
                            offset = ((LongValue) offsetValue).getValue();
                        } else if (offsetValue instanceof Long) {
                            offset = (Long) offsetValue;
                        } else if (offsetValue != null) {
                            offset = Long.parseLong(offsetValue.toString());
                        }
                    } catch (Exception e) {
                        // 如果反射失败，尝试从 toString() 解析
                        String offsetStr = offsetObj.toString();
                        Pattern offsetPattern = Pattern.compile("(?i)OFFSET\\s+(\\d+)\\s+ROWS?", Pattern.CASE_INSENSITIVE);
                        Matcher m = offsetPattern.matcher(offsetStr);
                        if (m.find()) {
                            offset = Long.parseLong(m.group(1));
                        }
                    }
                }
            } catch (Exception e) {
                // getOffset() 方法不存在或失败，忽略
            }
            
            // 获取 FETCH（如果存在）
            try {
                Method getFetchMethod = PlainSelect.class.getMethod("getFetch");
                Object fetchObj = getFetchMethod.invoke(plainSelect);
                if (fetchObj != null) {
                    // Fetch 对象有 getExpression() 方法返回 LongValue
                    try {
                        Method getExpressionMethod = fetchObj.getClass().getMethod("getExpression");
                        Object exprObj = getExpressionMethod.invoke(fetchObj);
                        if (exprObj instanceof LongValue) {
                            rowCount = ((LongValue) exprObj).getValue();
                        } else if (exprObj instanceof Long) {
                            rowCount = (Long) exprObj;
                        } else if (exprObj != null) {
                            rowCount = Long.parseLong(exprObj.toString());
                        }
                    } catch (Exception e) {
                        // 如果反射失败，尝试从 toString() 解析
                        String fetchStr = fetchObj.toString();
                        Pattern fetchPattern = Pattern.compile("(?i)FETCH\\s+(?:FIRST|NEXT)\\s+(\\d+)\\s+ROWS\\s+ONLY", Pattern.CASE_INSENSITIVE);
                        Matcher m = fetchPattern.matcher(fetchStr);
                        if (m.find()) {
                            rowCount = Long.parseLong(m.group(1));
                        }
                    }
                }
            } catch (Exception e) {
                // getFetch() 方法不存在或失败，忽略
            }
            
            // 如果有分页信息，生成 PostgreSQL 的 LIMIT/OFFSET 语句
            if (rowCount > 0) {
                sb.append(" LIMIT ").append(rowCount);
            }
            if (offset > 0) {
                sb.append(" OFFSET ").append(offset);
            }
            
            sb.append(";\n\n");
        } else {
            // 非 PlainSelect，直接转换
            String selectStr = select.toString();
            selectStr = convertOracleFunctions(selectStr);
            sb.append(selectStr).append(";\n\n");
        }
        
        return sb.toString();
    }

    /**
     * 将 Oracle 表达式中常见函数/语法转换为 PostgreSQL 风格
     */
    private String convertOracleFunctions(String sql) {
        if (sql == null) return "";
        String result = sql;
        // SYSDATE -> CURRENT_TIMESTAMP
        result = result.replaceAll("(?i)\\bSYSDATE\\b", "CURRENT_TIMESTAMP");
        // SYSTIMESTAMP -> CURRENT_TIMESTAMP
        result = result.replaceAll("(?i)\\bSYSTIMESTAMP\\b", "CURRENT_TIMESTAMP");
        // TO_DATE -> TO_TIMESTAMP
        result = result.replaceAll("(?i)\\bTO_DATE\\s*\\(", "TO_TIMESTAMP(");
        // NVL -> COALESCE
        result = result.replaceAll("(?i)\\bNVL\\s*\\(", "COALESCE(");
        
        // INTERVAL 转换（Oracle: INTERVAL '365' DAY，PostgreSQL: INTERVAL '365 days'）
        // PostgreSQL 的 INTERVAL 格式是 '数值 单位'，单位可以是复数形式
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+YEAR", "INTERVAL '$1 years'");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+MONTH", "INTERVAL '$1 months'");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+DAY", "INTERVAL '$1 days'");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+HOUR", "INTERVAL '$1 hours'");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+MINUTE", "INTERVAL '$1 minutes'");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+SECOND", "INTERVAL '$1 seconds'");
        
        // 标识符双引号保持（PostgreSQL 使用双引号）
        // 去掉反引号，转为双引号
        result = result.replace("`", "\"");
        return result;
    }

    /**
     * 转换表达式（处理 Oracle 函数、INTERVAL、SYSDATE 等）
     */
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

            // 特殊处理 Oracle 函数
            if ("TO_DATE".equalsIgnoreCase(functionName) && params != null && params.size() >= 2) {
                String dateStr = params.get(0).toString();
                String oracleFormat = params.get(1).toString().replaceAll("['\"]", "");
                // PostgreSQL 使用 TO_TIMESTAMP，格式字符串类似
                return "TO_TIMESTAMP(" + dateStr + ", " + "'" + oracleFormat + "')";
            } else if ("SYSDATE".equalsIgnoreCase(functionName)) {
                return "CURRENT_TIMESTAMP";
            } else if ("SYSTIMESTAMP".equalsIgnoreCase(functionName)) {
                return "CURRENT_TIMESTAMP";
            } else if ("NVL".equalsIgnoreCase(functionName) && params != null && params.size() == 2) {
                return "COALESCE(" + convertExpression(params.get(0)) + ", " + convertExpression(params.get(1)) + ")";
            }

            // 其他函数
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
            String colName = column.getColumnName();
            // 特殊处理：SYSDATE 被解析为 Column 而不是 Function
            if ("SYSDATE".equalsIgnoreCase(colName) || "SYSTIMESTAMP".equalsIgnoreCase(colName)) {
                return "CURRENT_TIMESTAMP";
            }
            return cleanIdentifier(colName);
        }

        // 处理 IntervalExpression（INTERVAL '365' DAY）
        try {
            // 检查是否是 IntervalExpression
            if (expression.getClass().getSimpleName().contains("Interval")) {
                String intervalStr = expression.toString();
                // 使用 convertOracleFunctions 处理 INTERVAL 转换
                intervalStr = convertOracleFunctions(intervalStr);
                return intervalStr;
            }
        } catch (Exception ignore) {}

        // 递归处理常见的表达式类型: 比如二元操作符等
        try {
            // 处理二元运算，如 AndExpression, EqualsTo 等
            Method getLeft = expression.getClass().getMethod("getLeftExpression");
            Method getRight = expression.getClass().getMethod("getRightExpression");
            Object left = getLeft.invoke(expression);
            Object right = getRight.invoke(expression);
            String op = expression.getClass().getSimpleName();
            String opStr;
            // 还原运算符 (适用于大部分JSqlParser)
            if (op.endsWith("AndExpression")) {
                opStr = " AND ";
            } else if (op.endsWith("OrExpression")) {
                opStr = " OR ";
            } else if (op.endsWith("EqualsTo")) {
                opStr = " = ";
            } else if (op.endsWith("NotEqualsTo")) {
                opStr = " <> ";
            } else if (op.endsWith("GreaterThan")) {
                opStr = " > ";
            } else if (op.endsWith("GreaterThanEquals")) {
                opStr = " >= ";
            } else if (op.endsWith("MinorThan")) {
                opStr = " < ";
            } else if (op.endsWith("MinorThanEquals")) {
                opStr = " <= ";
            } else if (op.endsWith("LikeExpression")) {
                opStr = " LIKE ";
            } else if (op.endsWith("InExpression")) {
                opStr = " IN ";
            } else if (op.contains("Subtraction") || op.contains("Minus")) {
                // 减法运算符
                opStr = " - ";
            } else if (op.contains("Addition") || op.contains("Plus")) {
                // 加法运算符
                opStr = " + ";
            } else if (op.contains("Multiplication")) {
                // 乘法运算符
                opStr = " * ";
            } else if (op.contains("Division")) {
                // 除法运算符
                opStr = " / ";
            } else if (op.endsWith("IsNullExpression")) {
                // IS NULL/IS NOT NULL表达式
                boolean not = false;
                try {
                    not = (boolean) expression.getClass().getMethod("isNot").invoke(expression);
                } catch (Exception ignore) {}
                return convertExpression((Expression) left) + (not ? " IS NOT NULL" : " IS NULL");
            } else {
                opStr = " " + op.replaceAll("Expression$", "") + " ";
            }
            return convertExpression((Expression) left) + opStr + convertExpression((Expression) right);
        } catch (Exception ignore) {}

        // 尝试括号表达式
        try {
            Method getExpr = expression.getClass().getMethod("getExpression");
            Object exprObj = getExpr.invoke(expression);
            return "(" + convertExpression((Expression) exprObj) + ")";
        } catch (Exception ignore) {}

        // 处理IN (xxx, yyy)结构
        try {
            Method getLeft = expression.getClass().getMethod("getLeftExpression");
            Object left = getLeft.invoke(expression);
            Method getRightItems = expression.getClass().getMethod("getRightItemsList");
            Object rightItems = getRightItems.invoke(expression);
            if (rightItems instanceof ExpressionList) {
                @SuppressWarnings("unchecked")
                List<Expression> exprs = ((ExpressionList) rightItems).getExpressions();
                StringBuilder sb = new StringBuilder();
                sb.append(convertExpression((Expression) left)).append(" IN (");
                for (int i = 0; i < exprs.size(); i++) {
                    if (i != 0) sb.append(", ");
                    sb.append(convertExpression(exprs.get(i)));
                }
                sb.append(")");
                return sb.toString();
            }
        } catch (Exception ignore) {}

        // 其他表达式 fallback
        // 先使用 convertOracleFunctions 处理 SYSDATE 和 INTERVAL
        String exprStr = expression.toString();
        exprStr = convertOracleFunctions(exprStr);
        return exprStr;
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
