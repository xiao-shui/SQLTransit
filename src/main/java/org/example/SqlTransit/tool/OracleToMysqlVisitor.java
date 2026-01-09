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

public class OracleToMysqlVisitor extends StatementVisitorAdapter {
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
    private final StringBuilder mysqlSql = new StringBuilder();

    // 收集所有信息，最后统一输出
    private static class TableInfo {
        String tableName;
        List<ColumnInfo> columns = new ArrayList<>();
        List<String> primaryKeys = new ArrayList<>();
        List<String> uniqueKeys = new ArrayList<>();
        String tableComment;
        boolean hasTableDefinition = false;

        // 获取字段信息，便于查找
        ColumnInfo getColumnInfo(String columnName) {
            for (ColumnInfo col : columns) {
                if (col.name.equals(columnName)) {
                    return col;
                }
            }
            return null;
        }
    }

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
    private final Map<String, String> columnComments = new HashMap<>(); // 存储列注释：table.column -> comment
    private final Map<String, String> tableComments = new HashMap<>(); // 存储表注释：table -> comment
    private final Map<String, Set<String>> tablePkColsMap = new HashMap<>(); // 表主键列集合，去模式名，用于去重索引

    private void addRawSql(String sql) {
        if (sql != null && !sql.isEmpty()) {
            chunks.add(new Chunk(sql));
        }
    }

    /**
     * 强制清洗标识符为小写（彻底移除引号，转为小写）
     */
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        // 移除所有引号/反引号，强制转小写
        return name.replaceAll("^[\"`']+|[\"`']+$", "").toLowerCase(Locale.ROOT).trim();
    }

    /**
     * 处理表名字符串，去掉schema部分，返回小写表名
     */
    private String getTableNameOnly(String raw) {
        if (raw == null) return null;
        // 去掉引号
        String s = raw.replaceAll("[\"`']", "");
        // 按点分割，取最后一部分作为表名
        String[] parts = s.split("\\.");
        String tableName = parts.length > 0 ? parts[parts.length - 1] : s;
        return tableName.toLowerCase(Locale.ROOT).trim();
    }

    /**
     * 去掉schema并清洗名称，返回小写索引名（不带反引号）
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
     * 列名参数全部小写（形如 id, code...）
     */
    private String parseAndJoinCols(String cols) {
        if (cols == null) return "";
        String[] arr = cols.split(",");
        List<String> result = new ArrayList<>();
        for (String c : arr) {
            result.add(cleanIdentifier(c.trim()));
        }
        return String.join(", ", result);
    }

    /**
     * 辅助方法：提取约束中的列名
     */
    private List<String> extractColumnNamesFromConstraint(String constraintStr) {
        List<String> columns = new ArrayList<>();
        Pattern pattern = Pattern.compile("\\(([^)]+)\\)");
        Matcher matcher = pattern.matcher(constraintStr);
        if (matcher.find()) {
            String cols = matcher.group(1);
            String[] colArray = cols.split(",");
            for (String col : colArray) {
                String cleanCol = col.replaceAll("[\"`']", "").trim().toLowerCase(Locale.ROOT);
                if (!cleanCol.isEmpty()) {
                    columns.add(cleanCol);
                }
            }
        }
        return columns;
    }

    private String convertDataType(String oracleType, List<String> args) {
        if (oracleType == null) return "VARCHAR(255)";
        String type = oracleType.toUpperCase(Locale.ROOT);
        switch (type) {
            case "NUMBER":
                if (args != null && args.size() == 2) {
                    // 处理 NUMBER(p,0) 的情况
                    try {
                        int scale = Integer.parseInt(args.get(1).trim());
                        if (scale == 0) {
                            // NUMBER(p,0) 根据精度转换为 INT 或 BIGINT
                            int precision = Integer.parseInt(args.get(0).trim());
                            if (precision <= 10) {
                                return "INT";
                            } else {
                                return "BIGINT";
                            }
                        } else {
                            // NUMBER(p,s) 其中 s != 0，转为 DECIMAL
                    return "DECIMAL(" + args.get(0) + "," + args.get(1) + ")";
                        }
                    } catch (NumberFormatException e) {
                        // 解析失败，回退为 DECIMAL
                        return "DECIMAL(" + args.get(0) + "," + args.get(1) + ")";
                    }
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

    @Override
    public void visit(Drop drop) {
        // 只关心 DROP TABLE，其它类型直接输出
        String type = drop.getType();
        if (type == null || !"TABLE".equalsIgnoreCase(type)) {
            addRawSql(drop.toString() + ";\n\n");
            return;
        }

        String tableName;
        if (drop.getName() != null) {
            tableName = cleanIdentifier(drop.getName().getName());
        } else {
            tableName = drop.toString().replaceAll("(?i)DROP\\s+TABLE\\s?", "").trim();
            tableName = cleanIdentifier(tableName);
        }

        addRawSql("DROP TABLE IF EXISTS "+tableName+";\n\n");
    }

    @Override
    public void visit(CreateTable createTable) {
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
                }

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
                        colInfo.isAutoIncrement = true;
                        break;
                    case "GENERATED":
                        if (j + 2 < columnSpecs.size()
                                && "BY".equalsIgnoreCase(columnSpecs.get(j + 1))
                                && "DEFAULT".equalsIgnoreCase(columnSpecs.get(j + 2))) {
                            colInfo.isAutoIncrement = true;
                            j += 2;
                        }
                        break;
                    case "COMMENT":
                        if (j + 1 < columnSpecs.size()) {
                            colInfo.columnComment = cleanCommentValue(columnSpecs.get(j + 1));
                            j++;
                        }
                        break;
                }
            }

            // 处理默认值转换
            if (colInfo.defaultValue != null) {
                if (colInfo.defaultValue.toUpperCase(Locale.ROOT).contains("SYSDATE") ||
                        colInfo.defaultValue.toUpperCase(Locale.ROOT).contains("CURRENT_TIMESTAMP")) {
                    colInfo.defaultValue = "CURRENT_TIMESTAMP";
                } else if (colInfo.defaultValue.toUpperCase(Locale.ROOT).contains("NULL")) {
                    colInfo.defaultValue = "NULL";
                }
            }

            // 检查是否已经存在此字段（可能来自之前的 COMMENT ON COLUMN）
            ColumnInfo existingCol = tableInfo.getColumnInfo(colInfo.name);
            if (existingCol != null) {
                // 合并字段信息：保留已有注释，更新其他属性
                existingCol.type = colInfo.type;
                existingCol.isPrimaryKey = colInfo.isPrimaryKey;
                existingCol.isUnique = colInfo.isUnique;
                existingCol.isNotNull = colInfo.isNotNull;
                existingCol.isAutoIncrement = colInfo.isAutoIncrement;
                existingCol.defaultValue = colInfo.defaultValue;
                existingCol.checkConstraint = colInfo.checkConstraint;
                // 如果当前有注释且已有注释为空，则使用当前注释
                if (colInfo.columnComment != null && (existingCol.columnComment == null || existingCol.columnComment.isEmpty())) {
                    existingCol.columnComment = colInfo.columnComment;
                }
            } else {
                // 添加新字段信息
                tableInfo.columns.add(colInfo);
            }
        }

         // 处理表级约束，将主键约束应用到相应字段上
         Set<String> tablePrimaryKeyCols = new LinkedHashSet<>();
         try {
             Method getIndexesMethod = CreateTable.class.getMethod("getIndexes");
             List<?> indexes = (List<?>) getIndexesMethod.invoke(createTable);
             if (indexes != null) {
                 for (Object idx : indexes) {
                     String idxStr = idx.toString().trim();
                     String idxStrUpper = idxStr.toUpperCase(Locale.ROOT);
                     if (idxStrUpper.contains("PRIMARY KEY")) {
                         List<String> pkCols = extractColumnNamesFromConstraint(idxStr);
                         if (pkCols != null && !pkCols.isEmpty()) {
                             tablePrimaryKeyCols.addAll(pkCols);
                             // 将表级主键约束应用到相应字段上
                             for (String pkCol : pkCols) {
                                 String cleanPkCol = pkCol.replaceAll("[\"`']", "").toLowerCase(Locale.ROOT);
                                 // 找到对应的字段并标记为主键
                                 for (ColumnInfo col : tableInfo.columns) {
                                     String cleanColName = col.name.replaceAll("[\"`']", "").toLowerCase(Locale.ROOT);
                                     if (cleanColName.equals(cleanPkCol)) {
                                         col.isPrimaryKey = true;
                                         // 添加到主键列表中（如果还没有）
                                         if (!tableInfo.primaryKeys.contains(col.name)) {
                                             tableInfo.primaryKeys.add(col.name);
                                         }
                                         break;
                                     }
                                 }
                             }
                         }
                     }
                 }
             }
         } catch (Exception ignore) {}

         // 如果列级主键存在，也加入到集合中
         for (String pkCol : tableInfo.primaryKeys) {
             String cleanPkCol = pkCol.replaceAll("[\"`']", "").toLowerCase(Locale.ROOT);
             tablePrimaryKeyCols.add(cleanPkCol);
         }

         // 存储到 tablePkColsMap 中（用于索引去重）
         if (!tablePrimaryKeyCols.isEmpty()) {
             Set<String> pkSet = new LinkedHashSet<>(tablePrimaryKeyCols);
             String normTableKey = tableName.replaceAll("[\"`']", "").toLowerCase(Locale.ROOT);
             tablePkColsMap.put(normTableKey, pkSet);
         }

         // 将 CREATE TABLE 添加到 chunks 中（延迟渲染）
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

            // 同时更新 TableInfo（如果已存在）
            TableInfo tableInfo = tables.get(tableName);
            if (tableInfo != null) {
                tableInfo.tableComment = commentTxt;
            }

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
                columnName = columnName.replaceAll("[\"`']", "").toLowerCase(Locale.ROOT).trim();

                // 存储到Map中，等待CREATE TABLE时使用
                String commentKey = tableName + "." + columnName;
                columnComments.put(commentKey, commentTxt);

                // 同时更新 ColumnInfo（如果已存在）
                TableInfo tableInfo = tables.get(tableName);
                if (tableInfo != null) {
                    ColumnInfo colInfo = tableInfo.getColumnInfo(columnName);
                    if (colInfo != null) {
                        colInfo.columnComment = commentTxt;
                    }
                }
            }
            return;
        }

        // 如果正则解析失败，尝试使用JSqlParser API作为fallback
        String commentText = null;
        if (comment.getComment() instanceof StringValue) {
            StringValue stringValue = (StringValue) comment.getComment();
            commentText = stringValue.getValue().trim();
        } else if (comment.getComment() != null) {
            commentText = cleanCommentValue(comment.getComment().toString());
        }
        if (commentText == null) commentText = "";

        if (comment.getTable() != null) {
            String tableName = cleanIdentifier(comment.getTable().getName());
            TableInfo tableInfo = tables.computeIfAbsent(tableName, k -> new TableInfo());
            tableInfo.tableName = tableName;

            // 字段注释
            if (comment.getColumn() != null) {
                String columnName = cleanIdentifier(comment.getColumn().getColumnName());
                ColumnInfo colInfo = tableInfo.getColumnInfo(columnName);
                if (colInfo == null) {
                    // 没找到，创建新字段信息（只有注释，其他属性后面会补充）
                    colInfo = new ColumnInfo();
                    colInfo.name = columnName;
                    tableInfo.columns.add(colInfo);
                }
                colInfo.columnComment = commentText;
                // 同时存储到Map中
                String commentKey = tableName + "." + columnName;
                columnComments.put(commentKey, commentText);
            } else {
                // 表注释
                tableInfo.tableComment = commentText;
                tableComments.put(tableName, commentText);
            }
        }
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

        // 如果是唯一索引且列集合与表主键一致，跳过创建（避免重复）
        String normTableKey = tableName.replaceAll("[\"`']", "").toLowerCase(Locale.ROOT);
        Set<String> pkCols = tablePkColsMap.get(normTableKey);
        if (isUnique && pkCols != null && !pkCols.isEmpty()) {
            Set<String> idxCols = new LinkedHashSet<>();
            for (String c : columns) {
                idxCols.add(c.replaceAll("[\"`']", "").toLowerCase(Locale.ROOT));
            }
            if (pkCols.equals(idxCols)) {
                return;
            }
        }

        StringBuilder sb = new StringBuilder();
        sb.append("CREATE");
        if (isUnique) sb.append(" UNIQUE");
        sb.append(" INDEX `").append(indexName).append("`")
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
            Method getTableMethod = Alter.class.getMethod("getTable");
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
        List<AlterExpression> expressions = null;
        try {
            Method getAlterExprMethod = Alter.class.getMethod("getAlterExpressions");
            Object alterExprsObj = getAlterExprMethod.invoke(alter);
            if (alterExprsObj instanceof List) {
                @SuppressWarnings("unchecked")
                List<AlterExpression> alterExprs = (List<AlterExpression>) alterExprsObj;
                expressions = alterExprs;
            }
        } catch (Exception e) {}
        if (expressions != null) {
            for (AlterExpression expr : expressions) {
                if (expr == null) continue;
                String opStr = expr.getOperation() != null ? expr.getOperation().toString().toUpperCase(Locale.ROOT) : "";
                if ("ADD".equals(opStr) && expr.getIndex() != null) {
                    Object idx = expr.getIndex();
                    String idxStr = idx.toString();
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
        String sql = convertInsert(insert);
        addRawSql(sql);
    }

    @Override
    public void visit(Update update) {
        String sql = convertUpdate(update);
        addRawSql(sql);
    }

    @Override
    public void visit(Delete delete) {
        String sql = convertDelete(delete);
        addRawSql(sql);
    }

    private String renderCreateTable(CreateTable createTable) {
        StringBuilder sb = new StringBuilder();
        // 如果存在 schema，则保留 schema.table
        String tableName = getFullTableName(createTable.getTable());
        TableInfo tableInfo = tables.get(tableName);
        if (tableInfo == null || !tableInfo.hasTableDefinition) {
            return "";
        }

        sb.append("CREATE TABLE ").append(tableInfo.tableName).append(" (\n");

        // 判断是否是单字段主键
        boolean isSingleColumnPrimaryKey = tableInfo.primaryKeys.size() == 1;

            for (int i = 0; i < tableInfo.columns.size(); i++) {
                ColumnInfo col = tableInfo.columns.get(i);
            if (i > 0) sb.append(",\n");

            sb.append("    ").append(col.name).append(" ").append(col.type);

                if (col.defaultValue != null) {
                sb.append(" DEFAULT ").append(col.defaultValue);
                }

                if (col.isAutoIncrement) {
                sb.append(" AUTO_INCREMENT");
                }

            // 只有单字段主键时，才在字段后面加 PRIMARY KEY
            if(col.isPrimaryKey && isSingleColumnPrimaryKey){
                sb.append(" PRIMARY KEY");
                }

                if (col.isNotNull) {
                sb.append(" NOT NULL");
                }

                if (col.isUnique) {
                sb.append(" UNIQUE");
                }

                if (col.checkConstraint != null && !col.checkConstraint.isEmpty()) {
                sb.append(" CHECK ").append(col.checkConstraint);
            }

            // 优先使用Map中的注释（从COMMENT ON COLUMN语句解析的），否则使用ColumnInfo中的注释
            String columnCommentKey = tableInfo.tableName + "." + col.name;
            String columnComment = columnComments.get(columnCommentKey);
            if (columnComment == null || columnComment.isEmpty()) {
                columnComment = col.columnComment;
            }
            if (columnComment != null && !columnComment.isEmpty()) {
                // 移除注释值中的引号（如果存在）
                if ((columnComment.startsWith("'") && columnComment.endsWith("'")) ||
                        (columnComment.startsWith("\"") && columnComment.endsWith("\""))) {
                    columnComment = columnComment.substring(1, columnComment.length() - 1);
                }
                sb.append(" COMMENT '").append(escapeComment(columnComment)).append("'");
            }
        }

        // 如果是复合主键，在最后添加 PRIMARY KEY 约束
        if (!tableInfo.primaryKeys.isEmpty() && !isSingleColumnPrimaryKey) {
            sb.append(",\n    PRIMARY KEY (");
            for (int i = 0; i < tableInfo.primaryKeys.size(); i++) {
                if (i > 0) sb.append(", ");
                sb.append(tableInfo.primaryKeys.get(i));
            }
            sb.append(")");
        }

        sb.append("\n)");

        // 优先使用Map中的表注释（从COMMENT ON TABLE语句解析的），否则使用TableInfo中的注释
        String tableComment = tableComments.get(tableInfo.tableName);
        if (tableComment == null || tableComment.isEmpty()) {
            tableComment = tableInfo.tableComment;
        }
        if (tableComment != null && !tableComment.isEmpty()) {
            // 移除注释值中的引号（如果存在）
            if ((tableComment.startsWith("'") && tableComment.endsWith("'")) ||
                    (tableComment.startsWith("\"") && tableComment.endsWith("\""))) {
                tableComment = tableComment.substring(1, tableComment.length() - 1);
            }
            sb.append(" COMMENT='").append(escapeComment(tableComment)).append("'");
        }

        sb.append(";\n\n");
        return sb.toString();
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
            sb.append(" WHERE ").append(convertExpressionLowerColumn(where));
        }

        return sb.append(";\n\n").toString();
    }

    private String convertDelete(Delete delete) {
        StringBuilder sb = new StringBuilder();
        String tableName = cleanIdentifier(delete.getTable().getName());
        sb.append("DELETE FROM ").append(tableName);

        Expression where = delete.getWhere();
        if (where != null) {
            sb.append(" WHERE ").append(convertExpressionLowerColumn(where));
        }

        return sb.append(";\n\n").toString();
    }

    /**
     * where后的表达式内容列名全部小写
     */
    private String convertExpressionLowerColumn(Expression expression) {
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

            // 特殊处理TO_DATE函数
            if ("TO_DATE".equalsIgnoreCase(functionName) && params != null && params.size() >= 2) {
                String dateStr = params.get(0).toString();
                String oracleFormat = params.get(1).toString().replaceAll("['\"]", "");
                String mysqlFormat = convertDateFormat(oracleFormat);
                return "STR_TO_DATE(" + dateStr + ", " + mysqlFormat + ")";
            }

            // 其他函数
            StringBuilder funcCall = new StringBuilder(functionName).append("(");
            if (params != null) {
                for (int i = 0; i < params.size(); i++) {
                    if (i > 0) funcCall.append(", ");
                    funcCall.append(convertExpressionLowerColumn(params.get(i)));
                }
            }
            funcCall.append(")");
            return funcCall.toString();
        }
        if (expression instanceof Column) {
            Column column = (Column) expression;
            return cleanIdentifier(column.getColumnName());
        }

        // 递归处理常见的表达式类型: 比如二元操作符等
        // 通过反射简化处理（如 left/right/operand/expressions），否则处理toString
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
            } else if (op.endsWith("IsNullExpression")) {
                // IS NULL/IS NOT NULL表达式
                boolean not = false;
                try {
                    not = (boolean) expression.getClass().getMethod("isNot").invoke(expression);
                } catch (Exception ignore) {}
                return convertExpressionLowerColumn((Expression) left) + (not ? " IS NOT NULL" : " IS NULL");
            } else {
                opStr = " " + op.replaceAll("Expression$", "") + " ";
            }
            return convertExpressionLowerColumn((Expression) left) + opStr + convertExpressionLowerColumn((Expression) right);
        } catch (Exception ignore) {}

        // 尝试括号表达式
        try {
            Method getExpr = expression.getClass().getMethod("getExpression");
            Object exprObj = getExpr.invoke(expression);
            return "(" + convertExpressionLowerColumn((Expression) exprObj) + ")";
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
                sb.append(convertExpressionLowerColumn((Expression) left)).append(" IN (");
                for (int i = 0; i < exprs.size(); i++) {
                    if (i != 0) sb.append(", ");
                    sb.append(convertExpressionLowerColumn(exprs.get(i)));
                }
                sb.append(")");
                return sb.toString();
            }
        } catch (Exception ignore) {}

        // 其他表达式 fallback
        // 尝试替换 identifier/列名为小写，提升兼容性
        String exprStr = expression.toString();
        // 用正则尽可能替换列名，仅替换未加引号、未作函数调用的写法, 不影响其他标识符
        // Java 8 前 Matcher 没有传入 lambda 的方法，因此需要自己用StringBuffer实现替换
        Pattern colNamePattern = Pattern.compile("([a-zA-Z_][a-zA-Z_0-9]*)");
        Matcher matcher = colNamePattern.matcher(exprStr);
        StringBuffer sb = new StringBuffer();
        while (matcher.find()) {
            matcher.appendReplacement(sb, matcher.group(1).toLowerCase());
        }
        matcher.appendTail(sb);
        exprStr = sb.toString();
        return exprStr;
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

            // 特殊处理TO_DATE函数
            if ("TO_DATE".equalsIgnoreCase(functionName) && params != null && params.size() >= 2) {
                String dateStr = params.get(0).toString();
                String oracleFormat = params.get(1).toString().replaceAll("['\"]", "");
                String mysqlFormat = convertDateFormat(oracleFormat);
                return "STR_TO_DATE(" + dateStr + ", " + mysqlFormat + ")";
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
            return cleanIdentifier(column.getColumnName());
        }

        // 处理其他表达式类型...
        return expression.toString();
    }

    private String convertDateFormat(String oracleFormat) {
        String format = oracleFormat.toUpperCase(Locale.ROOT);
        Map<String, String> formatMap = new HashMap<>();
        formatMap.put("YYYY", "%Y");
        formatMap.put("YY", "%y");
        formatMap.put("MM", "%m");
        formatMap.put("DD", "%d");
        formatMap.put("HH24", "%H");
        formatMap.put("HH", "%h");
        formatMap.put("MI", "%i");
        formatMap.put("SS", "%s");

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
        mysqlSql.setLength(0);
        chunks.clear();
        tables.clear();
        otherStatements.clear();
        columnComments.clear();
        tableComments.clear();
        tablePkColsMap.clear();
    }
}