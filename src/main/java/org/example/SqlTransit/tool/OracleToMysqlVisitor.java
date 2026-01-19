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
import net.sf.jsqlparser.statement.select.Select;
import net.sf.jsqlparser.statement.select.PlainSelect;

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
        List<CheckConstraintInfo> checkConstraints = new ArrayList<>(); // 表级 CHECK 约束
        String tableComment;
        boolean hasTableDefinition = false;
        // 是否存在表级 PRIMARY KEY 约束（包括 NamedConstraint 和普通 PRIMARY KEY (...)）
        boolean hasTablePrimaryKeyConstraint = false;

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

    private static class CheckConstraintInfo {
        String constraintName;
        Expression expression;
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
        tableInfo.hasTablePrimaryKeyConstraint = false;

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
                        colInfo.defaultValue.toUpperCase(Locale.ROOT).contains("SYSTIMESTAMP")) {
                    colInfo.defaultValue = "NOW()";
                } else if (colInfo.defaultValue.toUpperCase(Locale.ROOT).contains("CURRENT_TIMESTAMP")) {
                    colInfo.defaultValue = "NOW()";
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
                     
                     // 处理 CHECK 约束
                     if (idx.getClass().getSimpleName().contains("CheckConstraint")) {
                         try {
                             CheckConstraintInfo checkInfo = new CheckConstraintInfo();
                             // 获取约束名称
                             try {
                                 Method getNameMethod = idx.getClass().getMethod("getName");
                                 Object nameObj = getNameMethod.invoke(idx);
                                 if (nameObj != null) {
                                     checkInfo.constraintName = cleanIdentifier(nameObj.toString());
                                 }
                             } catch (Exception e) {
                                 // 如果没有名称，使用默认名称
                             }
                             // 获取约束表达式
                             try {
                                 Method getExpressionMethod = idx.getClass().getMethod("getExpression");
                                 Object exprObj = getExpressionMethod.invoke(idx);
                                 if (exprObj instanceof Expression) {
                                     checkInfo.expression = (Expression) exprObj;
                                 }
                             } catch (Exception e) {
                                 // 如果获取表达式失败，尝试从 toString() 解析
                             }
                             if (checkInfo.expression != null) {
                                 tableInfo.checkConstraints.add(checkInfo);
                             }
                         } catch (Exception e) {
                             // 处理失败，忽略
                         }
                         continue;
                     }
                     
                    // 处理 NamedConstraint (带名称的主键约束)
                    if (idx.getClass().getSimpleName().contains("NamedConstraint") || 
                        (idxStrUpper.contains("PRIMARY KEY") && idxStrUpper.contains("CONSTRAINT"))) {
                        // 标记存在表级主键约束（来自 CONSTRAINT）
                        tableInfo.hasTablePrimaryKeyConstraint = true;
                         List<String> pkCols = new ArrayList<>();
                         
                         // 尝试通过 API 获取约束信息
                         // 注意：MySQL 的 CREATE TABLE 中主键约束名称通常不输出，所以不获取约束名称
                         try {
                             // 获取列名
                             try {
                                 Method getColumnsNamesMethod = idx.getClass().getMethod("getColumnsNames");
                                 Object colsObj = getColumnsNamesMethod.invoke(idx);
                                 if (colsObj instanceof List) {
                                     @SuppressWarnings("unchecked")
                                     List<String> cols = (List<String>) colsObj;
                                     if (cols != null) {
                                         for (String col : cols) {
                                             pkCols.add(cleanIdentifier(col));
                                         }
                                     }
                                 }
                             } catch (Exception e) {
                                 // 尝试 getColumns() 方法
                                 try {
                                     Method getColumnsMethod = idx.getClass().getMethod("getColumns");
                                     Object colsObj = getColumnsMethod.invoke(idx);
                                     if (colsObj instanceof List) {
                                         @SuppressWarnings("unchecked")
                                         List<?> cols = (List<?>) colsObj;
                                         if (cols != null) {
                                             for (Object colObj : cols) {
                                                 if (colObj instanceof Column) {
                                                     pkCols.add(cleanIdentifier(((Column) colObj).getColumnName()));
                                                 } else if (colObj instanceof String) {
                                                     pkCols.add(cleanIdentifier((String) colObj));
                                                 }
                                             }
                                         }
                                     }
                                 } catch (Exception e2) {
                                     // 如果都失败，使用正则表达式解析
                                     pkCols = extractColumnNamesFromConstraint(idxStr);
                                 }
                             }
                         } catch (Exception e) {
                             // 如果 API 调用失败，使用正则表达式解析
                             pkCols = extractColumnNamesFromConstraint(idxStr);
                         }
                         
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
                             // 存储约束名称（如果需要的话，可以在 renderCreateTable 中使用）
                             // 注意：MySQL 的 CREATE TABLE 中，主键约束名称通常不输出，但可以在 ALTER TABLE 中使用
                         }
                         continue;
                     }
                     
                    // 处理普通的 PRIMARY KEY 约束（没有名称或不是 NamedConstraint）
                    if (idxStrUpper.contains("PRIMARY KEY")) {
                        // 也视为表级主键约束
                        tableInfo.hasTablePrimaryKeyConstraint = true;
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
        boolean processed = false; // 标记是否成功处理了任何表达式
        
        if (expressions != null) {
            for (AlterExpression expr : expressions) {
                if (expr == null) continue;
                String opStr = expr.getOperation() != null ? expr.getOperation().toString().toUpperCase(Locale.ROOT) : "";
                
                // 处理 ADD COLUMN、MODIFY COLUMN、CHANGE COLUMN 等涉及数据类型的操作
                if ("ADD".equals(opStr) || "MODIFY".equals(opStr)) {
                    // 尝试通过反射获取getColDataTypeList
                    try {
                        Method getColDataTypeListMethod = expr.getClass().getMethod("getColDataTypeList");
                        Object colDataTypeListObj = getColDataTypeListMethod.invoke(expr);
                        
                        if (colDataTypeListObj instanceof List && !((List<?>) colDataTypeListObj).isEmpty()) {
                            Object colDataTypeObj = ((List<?>) colDataTypeListObj).get(0);
                            
                            // 获取列名和数据类型
                            String colName = null;
                            String colType = null;
                            List<String> args = null;
                            
                            // 尝试获取ColDataType
                            try {
                                Method getColDataTypeMethod = colDataTypeObj.getClass().getMethod("getColDataType");
                                Object colDataType = getColDataTypeMethod.invoke(colDataTypeObj);
                                
                                if (colDataType != null) {
                                    // 获取数据类型名
                                    Method getDataTypeMethod = colDataType.getClass().getMethod("getDataType");
                                    Object dataTypeObj = getDataTypeMethod.invoke(colDataType);
                                    if (dataTypeObj != null) {
                                        colType = dataTypeObj.toString();
                                    }
                                    
                                    // 获取参数
                                    try {
                                        Method getArgumentsMethod = colDataType.getClass().getMethod("getArgumentsStringList");
                                        Object argsObj = getArgumentsMethod.invoke(colDataType);
                                        if (argsObj instanceof List) {
                                            @SuppressWarnings("unchecked")
                                            List<String> argsList = (List<String>) argsObj;
                                            args = argsList;
                                        }
                                    } catch (Exception e) {
                                        // 忽略
                                    }
                                }
                            } catch (Exception e) {
                                // 忽略
                            }
                            
                            // 从toString中提取列名和完整信息
                            String colDataTypeStr = colDataTypeObj.toString();
                            
                            // 提取列名（第一个单词，在数据类型之前）
                            Pattern colNamePattern = Pattern.compile("^\\s*([`'\"]?\\w+[`'\"]?)\\s+([A-Z_]+)", Pattern.CASE_INSENSITIVE);
                            Matcher colNameMatcher = colNamePattern.matcher(colDataTypeStr);
                            if (colNameMatcher.find()) {
                                colName = cleanIdentifier(colNameMatcher.group(1));
                                if (colType == null) {
                                    colType = colNameMatcher.group(2).toUpperCase(Locale.ROOT);
                                }
                            }
                            
                            // 如果无法从模式匹配获取，尝试从字符串解析
                            if (colName == null) {
                                String[] parts = colDataTypeStr.trim().split("\\s+");
                                if (parts.length > 0) {
                                    colName = cleanIdentifier(parts[0]);
                                }
                            }
                            
                            // 转换数据类型
                            if (colType != null && colName != null) {
                                String mysqlType = convertDataType(colType, args);
                                
                                StringBuilder sb = new StringBuilder();
                                sb.append("ALTER TABLE ").append(tableName).append(" ");
                                
                                if ("ADD".equals(opStr)) {
                                    sb.append("ADD COLUMN ");
                                } else if ("MODIFY".equals(opStr)) {
                                    sb.append("MODIFY COLUMN ");
                                }
                                
                                sb.append(colName).append(" ").append(mysqlType);
                                
                                // 处理列规格（从getColumnSpecs获取）
                                try {
                                    Method getColumnSpecsMethod = colDataTypeObj.getClass().getMethod("getColumnSpecs");
                                    Object specsObj = getColumnSpecsMethod.invoke(colDataTypeObj);
                                    if (specsObj instanceof List) {
                                        List<String> specs = new ArrayList<>();
                                        for (Object spec : (List<?>) specsObj) {
                                            if (spec != null) {
                                                specs.add(spec.toString().trim());
                                            }
                                        }
                                        
                                        // 解析约束
                                        boolean isNotNull = false;
                                        String defaultVal = null;
                                        
                                        for (int i = 0; i < specs.size(); i++) {
                                            String spec = specs.get(i).toUpperCase(Locale.ROOT).trim();
                                            
                                            // 检查两词组合
                                            if (i + 1 < specs.size()) {
                                                String twoWordSpec = spec + " " + specs.get(i + 1).toUpperCase(Locale.ROOT).trim();
                                                if ("NOT NULL".equals(twoWordSpec)) {
                                                    isNotNull = true;
                                                    i++; // 跳过NULL
                                                    continue;
                                                }
                                            }
                                            
                                            // 检查单词约束
                                            if ("DEFAULT".equals(spec) && i + 1 < specs.size()) {
                                                defaultVal = specs.get(i + 1);
                                                i++; // 跳过默认值
                                            } else if ("NOT".equals(spec) && i + 1 < specs.size() && "NULL".equals(specs.get(i + 1).toUpperCase(Locale.ROOT).trim())) {
                                                isNotNull = true;
                                                i++; // 跳过NULL
                                            }
                                        }
                                        
                                        // 添加约束
                                        if (defaultVal != null && !"NULL".equalsIgnoreCase(defaultVal)) {
                                            // 转换Oracle默认值到MySQL
                                            if (defaultVal.toUpperCase(Locale.ROOT).contains("SYSDATE") ||
                                                    defaultVal.toUpperCase(Locale.ROOT).contains("SYSTIMESTAMP")) {
                                                sb.append(" DEFAULT NOW()");
                                            } else if (defaultVal.toUpperCase(Locale.ROOT).contains("CURRENT_TIMESTAMP")) {
                                                sb.append(" DEFAULT CURRENT_TIMESTAMP");
                                            } else {
                                                sb.append(" DEFAULT ").append(defaultVal);
                                            }
                                        }
                                        if (isNotNull) {
                                            sb.append(" NOT NULL");
                                        }
                                    }
                                } catch (Exception e) {
                                    // 如果无法获取列规格，尝试从字符串解析
                                    if (colDataTypeStr.toUpperCase(Locale.ROOT).contains("NOT NULL")) {
                                        sb.append(" NOT NULL");
                                    }
                                    Pattern defaultPattern = Pattern.compile("(?i)DEFAULT\\s+([^\\s]+(?:\\s+[^\\s]+)*?)(?=\\s+(?:NOT|NULL|,|$))");
                                    Matcher defaultMatcher = defaultPattern.matcher(colDataTypeStr);
                                    if (defaultMatcher.find()) {
                                        String defaultVal = defaultMatcher.group(1).trim();
                                        if (!"NULL".equalsIgnoreCase(defaultVal)) {
                                            if (defaultVal.toUpperCase(Locale.ROOT).contains("SYSDATE") ||
                                                    defaultVal.toUpperCase(Locale.ROOT).contains("SYSTIMESTAMP")) {
                                                sb.append(" DEFAULT NOW()");
                                            } else {
                                                sb.append(" DEFAULT ").append(defaultVal);
                                            }
                                        }
                                    }
                                }
                                
                                sb.append(";\n\n");
                                addRawSql(sb.toString());
                                processed = true;
                                continue;
                            }
                        }
                    } catch (Exception e) {
                        // 如果反射失败，尝试从toString()解析
                    }
                }
                
                // 处理 RENAME COLUMN ... TO ...
                if ("RENAME".equals(opStr)) {
                    try {
                        String exprStr = expr.toString();
                        // 匹配 RENAME COLUMN old_name TO new_name
                        Pattern renamePattern = Pattern.compile("(?i)RENAME\\s+COLUMN\\s+([`'\"]?\\w+[`'\"]?)\\s+TO\\s+([`'\"]?\\w+[`'\"]?)", Pattern.CASE_INSENSITIVE);
                        Matcher renameMatcher = renamePattern.matcher(exprStr);
                        if (renameMatcher.find()) {
                            String oldColName = cleanIdentifier(renameMatcher.group(1));
                            String newColName = cleanIdentifier(renameMatcher.group(2));
                            
                            // MySQL 8.0.2+ 支持 RENAME COLUMN 语法，与 Oracle 相同
                            StringBuilder sb = new StringBuilder();
                            sb.append("ALTER TABLE ").append(tableName)
                                    .append(" RENAME COLUMN ").append(oldColName)
                                    .append(" TO ").append(newColName)
                                    .append(";\n\n");
                            addRawSql(sb.toString());
                            processed = true;
                            continue;
                        }
                    } catch (Exception e) {
                        // 忽略异常
                    }
                }
                
                // 处理 DROP COLUMN
                if ("DROP".equals(opStr)) {
                    String colName = null;
                    
                    // 方法1：尝试通过反射获取列名
                    try {
                        Method getColDataTypeListMethod = expr.getClass().getMethod("getColDataTypeList");
                        Object colDataTypeListObj = getColDataTypeListMethod.invoke(expr);
                        
                        if (colDataTypeListObj instanceof List && !((List<?>) colDataTypeListObj).isEmpty()) {
                            Object colDataTypeObj = ((List<?>) colDataTypeListObj).get(0);
                            String colDataTypeStr = colDataTypeObj.toString();
                            
                            // 提取列名（第一个单词）
                            Pattern colNamePattern = Pattern.compile("^\\s*([`'\"]?\\w+[`'\"]?)", Pattern.CASE_INSENSITIVE);
                            Matcher colNameMatcher = colNamePattern.matcher(colDataTypeStr);
                            if (colNameMatcher.find()) {
                                colName = cleanIdentifier(colNameMatcher.group(1));
                            }
                        }
                    } catch (Exception e) {
                        // 忽略，继续尝试其他方法
                    }
                    
                    // 方法2：如果方法1失败，从toString()解析
                    if (colName == null || colName.isEmpty()) {
                        try {
                            String exprStr = expr.toString();
                            // 匹配 DROP COLUMN column_name
                            Pattern dropPattern = Pattern.compile("(?i)DROP\\s+COLUMN\\s+([`'\"]?\\w+[`'\"]?)", Pattern.CASE_INSENSITIVE);
                            Matcher dropMatcher = dropPattern.matcher(exprStr);
                            if (dropMatcher.find()) {
                                colName = cleanIdentifier(dropMatcher.group(1));
                            }
                        } catch (Exception e) {
                            // 忽略
                        }
                    }
                    
                    // 方法3：如果前两种方法都失败，尝试更宽松的正则表达式
                    if (colName == null || colName.isEmpty()) {
                        try {
                            String exprStr = expr.toString();
                            // 匹配 DROP COLUMN 后面的任何标识符
                            Pattern dropPattern = Pattern.compile("(?i)DROP\\s+COLUMN\\s+([^\\s,;]+)", Pattern.CASE_INSENSITIVE);
                            Matcher dropMatcher = dropPattern.matcher(exprStr);
                            if (dropMatcher.find()) {
                                String rawColName = dropMatcher.group(1).trim();
                                colName = cleanIdentifier(rawColName);
                            }
                        } catch (Exception e) {
                            // 忽略
                        }
                    }
                    
                    // 如果成功获取到列名，生成SQL
                    if (colName != null && !colName.isEmpty()) {
                        StringBuilder sb = new StringBuilder();
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" DROP COLUMN ").append(colName)
                                .append(";\n\n");
                        addRawSql(sb.toString());
                        processed = true;
                        continue;
                    }
                }
                
                if ("ADD".equals(opStr)) {
                    // 优先使用 getPkColumns() 方法直接获取主键列
                    List<String> pkColumns = null;
                    try {
                        Method getPkColumnsMethod = AlterExpression.class.getMethod("getPkColumns");
                        Object pkColsObj = getPkColumnsMethod.invoke(expr);
                        if (pkColsObj instanceof List) {
                            @SuppressWarnings("unchecked")
                            List<String> pkCols = (List<String>) pkColsObj;
                            if (pkCols != null && !pkCols.isEmpty()) {
                                pkColumns = pkCols;
                            }
                        }
                    } catch (Exception e) {
                        // getPkColumns() 方法不存在或失败，继续使用正则表达式解析
                    }
                    
                    // 如果通过 getPkColumns() 获取到主键列，直接构建 SQL
                    if (pkColumns != null && !pkColumns.isEmpty()) {
                        StringBuilder sb = new StringBuilder();
                        sb.append("ALTER TABLE ").append(tableName)
                                .append(" ADD PRIMARY KEY (");
                        List<String> cleanedCols = new ArrayList<>();
                        for (String col : pkColumns) {
                            cleanedCols.add(cleanIdentifier(col));
                        }
                        sb.append(String.join(", ", cleanedCols))
                                .append(");\n\n");
                        addRawSql(sb.toString());
                        continue;
                    }
                    
                    // 如果没有通过 getPkColumns() 获取到，继续使用原有的正则表达式解析方式
                    if (expr.getIndex() != null) {
                        Object idx = expr.getIndex();
                        
                        // 处理 CheckConstraint 对象
                        if (idx.getClass().getSimpleName().contains("CheckConstraint")) {
                            try {
                                StringBuilder sb = new StringBuilder();
                                sb.append("ALTER TABLE ").append(tableName).append(" ADD ");
                                
                                // 获取约束名称
                                try {
                                    Method getNameMethod = idx.getClass().getMethod("getName");
                                    Object nameObj = getNameMethod.invoke(idx);
                                    if (nameObj != null) {
                                        String constraintName = cleanIdentifier(nameObj.toString());
                                        if (!constraintName.isEmpty()) {
                                            sb.append("CONSTRAINT `").append(constraintName).append("` ");
                                        }
                                    }
                                } catch (Exception e) {
                                    // 如果没有名称，继续
                                }
                                
                                // 获取约束表达式
                                sb.append("CHECK (");
                                try {
                                    Method getExpressionMethod = idx.getClass().getMethod("getExpression");
                                    Object exprObj = getExpressionMethod.invoke(idx);
                                    if (exprObj instanceof Expression) {
                                        sb.append(convertExpressionLowerColumn((Expression) exprObj));
                                    } else {
                                        sb.append(exprObj != null ? exprObj.toString() : "");
                                    }
                                } catch (Exception e) {
                                    // 如果获取表达式失败，尝试从 toString() 解析
                                    String idxStr = idx.toString();
                                    Pattern checkPattern = Pattern.compile(
                                            "CHECK\\s*\\((.+)\\)",
                                            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
                                    Matcher checkMatcher = checkPattern.matcher(idxStr);
                                    if (checkMatcher.find()) {
                                        sb.append(checkMatcher.group(1).trim());
                                    }
                                }
                                sb.append(");\n\n");
                                addRawSql(sb.toString());
                                continue;
                            } catch (Exception e) {
                                // 处理失败，继续使用正则表达式
                            }
                        }
                        
                        // 处理 NamedConstraint (带名称的主键约束)
                        // 注意：MySQL 不支持主键约束名称，所以忽略约束名称，直接添加 PRIMARY KEY
                        if (idx.getClass().getSimpleName().contains("NamedConstraint")) {
                            try {
                                StringBuilder sb = new StringBuilder();
                                sb.append("ALTER TABLE ").append(tableName).append(" ADD ");
                                
                                // 获取列名（MySQL 不支持主键约束名称，所以不获取约束名称）
                                List<String> pkCols = new ArrayList<>();
                                try {
                                    Method getColumnsNamesMethod = idx.getClass().getMethod("getColumnsNames");
                                    Object colsObj = getColumnsNamesMethod.invoke(idx);
                                    if (colsObj instanceof List) {
                                        @SuppressWarnings("unchecked")
                                        List<String> cols = (List<String>) colsObj;
                                        if (cols != null) {
                                            for (String col : cols) {
                                                pkCols.add(cleanIdentifier(col));
                                            }
                                        }
                                    }
                                } catch (Exception e) {
                                    // 尝试 getColumns() 方法
                                    try {
                                        Method getColumnsMethod = idx.getClass().getMethod("getColumns");
                                        Object colsObj = getColumnsMethod.invoke(idx);
                                        if (colsObj instanceof List) {
                                            @SuppressWarnings("unchecked")
                                            List<?> cols = (List<?>) colsObj;
                                            if (cols != null) {
                                                for (Object colObj : cols) {
                                                    if (colObj instanceof Column) {
                                                        pkCols.add(cleanIdentifier(((Column) colObj).getColumnName()));
                                                    } else if (colObj instanceof String) {
                                                        pkCols.add(cleanIdentifier((String) colObj));
                                                    }
                                                }
                                            }
                                        }
                                    } catch (Exception e2) {
                                        // 如果都失败，使用正则表达式解析
                                        String idxStr = idx.toString();
                                        Pattern pkPattern = Pattern.compile(
                                                "PRIMARY\\s+KEY\\s*\\(([^)]+)\\)",
                                                Pattern.CASE_INSENSITIVE);
                                        Matcher pkMatcher = pkPattern.matcher(idxStr);
                                        if (pkMatcher.find()) {
                                            String cols = pkMatcher.group(1);
                                            String[] colArr = cols.split(",");
                                            for (String c : colArr) {
                                                pkCols.add(cleanIdentifier(c.trim()));
                                            }
                                        }
                                    }
                                }
                                
                                if (!pkCols.isEmpty()) {
                                    sb.append("PRIMARY KEY (")
                                            .append(String.join(", ", pkCols))
                                            .append(");\n\n");
                                    addRawSql(sb.toString());
                                    continue;
                                }
                            } catch (Exception e) {
                                // 处理失败，继续使用正则表达式
                            }
                        }
                        
                        String idxStr = idx.toString();
                        StringBuilder sb = new StringBuilder();
                        Pattern pkPattern = Pattern.compile(
                                "CONSTRAINT\\s+([`'\"]?\\w+[`'\"]?)?\\s*PRIMARY KEY\\s*\\(([^)]+)\\)",
                                Pattern.CASE_INSENSITIVE);
                        Matcher pkMatcher = pkPattern.matcher(idxStr);
                        if (pkMatcher.find()) {
                            // MySQL 不支持主键约束名称，所以忽略约束名称
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
            }
            
            // 如果成功处理了任何表达式，直接返回，不再执行后续逻辑
            if (processed) {
                return;
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

    @Override
    @SuppressWarnings("deprecation")
    public void visit(Select select) {
        String sql = convertSelect(select);
        addRawSql(sql);
    }

    private String renderCreateTable(CreateTable createTable) {
        StringBuilder sb = new StringBuilder();
        // 保留 schema.table，如果存在 schema
        String tableKey = cleanIdentifier(createTable.getTable().getName());
        String tableName = getFullTableName(createTable.getTable());
        TableInfo tableInfo = tables.get(tableKey);
        if (tableInfo == null || !tableInfo.hasTableDefinition) {
            return "";
        }

        sb.append("CREATE TABLE ").append(tableName).append(" (\n");

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

            // 只有在「不存在表级主键约束」且是单字段主键时，才在字段后面加 PRIMARY KEY
            // 如果 Oracle 使用了表级 CONSTRAINT ... PRIMARY KEY (...)，则只在表级输出主键，不在字段后追加
            if (col.isPrimaryKey && isSingleColumnPrimaryKey && !tableInfo.hasTablePrimaryKeyConstraint) {
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

        // 如果需要表级 PRIMARY KEY 约束，在最后添加：
        // 1）复合主键（多个字段）
        // 2）单字段主键但存在表级主键约束（来自 CONSTRAINT PRIMARY KEY）
        if (!tableInfo.primaryKeys.isEmpty()) {
            boolean needTableLevelPk =
                    !isSingleColumnPrimaryKey || tableInfo.hasTablePrimaryKeyConstraint;
            if (needTableLevelPk) {
                sb.append(",\n    PRIMARY KEY (");
                for (int i = 0; i < tableInfo.primaryKeys.size(); i++) {
                    if (i > 0) sb.append(", ");
                    sb.append(tableInfo.primaryKeys.get(i));
                }
                sb.append(")");
            }
        }

        // 添加表级 CHECK 约束
        for (CheckConstraintInfo checkInfo : tableInfo.checkConstraints) {
            sb.append(",\n    ");
            if (checkInfo.constraintName != null && !checkInfo.constraintName.isEmpty()) {
                sb.append("CONSTRAINT `").append(checkInfo.constraintName).append("` ");
            }
            sb.append("CHECK (");
            if (checkInfo.expression != null) {
                sb.append(convertExpressionLowerColumn(checkInfo.expression));
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
        
        // 检查是否有ORDER BY和LIMIT，MySQL支持这些特性
        boolean hasOrderBy = false;
        boolean hasLimit = false;
        long rowCount = 0;
        
        try {
            Method getOrderByMethod = delete.getClass().getMethod("getOrderByElements");
            Object orderByObj = getOrderByMethod.invoke(delete);
            hasOrderBy = orderByObj != null && orderByObj instanceof List && !((List<?>) orderByObj).isEmpty();
        } catch (Exception e) {
            // 忽略
        }
        
        try {
            Method getLimitMethod = delete.getClass().getMethod("getLimit");
            Object limitObj = getLimitMethod.invoke(delete);
            if (limitObj != null) {
                hasLimit = true;
                try {
                    Method getRowCountMethod = limitObj.getClass().getMethod("getRowCount");
                    Object rowCountObj = getRowCountMethod.invoke(limitObj);
                    if (rowCountObj instanceof net.sf.jsqlparser.expression.LongValue) {
                        rowCount = ((net.sf.jsqlparser.expression.LongValue) rowCountObj).getValue();
                    } else if (rowCountObj instanceof Long) {
                        rowCount = (Long) rowCountObj;
                    } else if (rowCountObj != null) {
                        rowCount = Long.parseLong(rowCountObj.toString());
                    }
                } catch (Exception e) {
                    // 忽略
                }
            }
        } catch (Exception e) {
            // 忽略
        }
        
        sb.append("DELETE FROM ").append(tableName);

        Expression where = delete.getWhere();
        if (where != null) {
            sb.append(" WHERE ").append(convertExpressionLowerColumn(where));
        }
        
        // 处理 ORDER BY
        if (hasOrderBy) {
            try {
                Method getOrderByMethod = delete.getClass().getMethod("getOrderByElements");
                Object orderByObj = getOrderByMethod.invoke(delete);
                if (orderByObj instanceof List) {
                    sb.append(" ORDER BY ");
                    boolean first = true;
                    for (Object orderElem : (List<?>) orderByObj) {
                        if (!first) sb.append(", ");
                        String orderStr = orderElem.toString();
                        orderStr = convertOracleFunctions(orderStr);
                        sb.append(orderStr);
                        first = false;
                    }
                }
            } catch (Exception e) {
                // 忽略
            }
        }
        
        // 处理 LIMIT
        if (hasLimit && rowCount > 0) {
            sb.append(" LIMIT ").append(rowCount);
        }

        return sb.append(";\n\n").toString();
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
                String whereStr = convertExpressionLowerColumn(plainSelect.getWhere());
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
            
            // 如果有分页信息，生成 MySQL 的 LIMIT 语句
            if (rowCount > 0) {
                if (offset > 0) {
                    // MySQL: LIMIT offset, rowCount (注意：MySQL 的 LIMIT 语法是 offset, count)
                    sb.append(" LIMIT ").append(offset).append(", ").append(rowCount);
                } else {
                    // MySQL: LIMIT rowCount
                    sb.append(" LIMIT ").append(rowCount);
                }
            } else if (offset > 0) {
                // 只有 OFFSET 没有 FETCH，这种情况不太常见，但也要处理
                sb.append(" LIMIT ").append(offset).append(", 18446744073709551615"); // MySQL 的最大值
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

            // 特殊处理 Oracle 函数
            if ("TO_DATE".equalsIgnoreCase(functionName) && params != null && params.size() >= 2) {
                String dateStr = params.get(0).toString();
                String oracleFormat = params.get(1).toString().replaceAll("['\"]", "");
                String mysqlFormat = convertDateFormat(oracleFormat);
                return "STR_TO_DATE(" + dateStr + ", " + mysqlFormat + ")";
            } else if ("SYSDATE".equalsIgnoreCase(functionName)) {
                return "NOW()";
            } else if ("SYSTIMESTAMP".equalsIgnoreCase(functionName)) {
                return "NOW()";
            } else if ("NVL".equalsIgnoreCase(functionName) && params != null && params.size() == 2) {
                return "IFNULL(" + convertExpressionLowerColumn(params.get(0)) + ", " + convertExpressionLowerColumn(params.get(1)) + ")";
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
            String colName = column.getColumnName();
            // 特殊处理：SYSDATE 被解析为 Column 而不是 Function
            if ("SYSDATE".equalsIgnoreCase(colName) || "SYSTIMESTAMP".equalsIgnoreCase(colName)) {
                return "NOW()";
            }
            return cleanIdentifier(colName);
        }

        // 处理 IntervalExpression（INTERVAL '365' DAY）
        try {
            // 检查是否是 IntervalExpression
            if (expression.getClass().getSimpleName().contains("Interval")) {
                String intervalStr = expression.toString();
                // 使用 convertOracleFunctions 处理 INTERVAL 转换（去掉引号）
                intervalStr = convertOracleFunctions(intervalStr);
                return intervalStr;
            }
        } catch (Exception ignore) {}

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
        // 先使用 convertOracleFunctions 处理 SYSDATE 和 INTERVAL
        String exprStr = expression.toString();
        exprStr = convertOracleFunctions(exprStr);
        
        // 尝试替换 identifier/列名为小写，提升兼容性
        // 用正则尽可能替换列名，仅替换未加引号、未作函数调用的写法, 不影响其他标识符
        // Java 8 前 Matcher 没有传入 lambda 的方法，因此需要自己用StringBuffer实现替换
        Pattern colNamePattern = Pattern.compile("([a-zA-Z_][a-zA-Z_0-9]*)");
        Matcher matcher = colNamePattern.matcher(exprStr);
        StringBuffer sb = new StringBuffer();
        while (matcher.find()) {
            String matched = matcher.group(1);
            // 跳过已经是 NOW() 的情况
            if (!matched.equalsIgnoreCase("NOW")) {
                matcher.appendReplacement(sb, matched.toLowerCase());
            } else {
                matcher.appendReplacement(sb, matched);
            }
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

            // 特殊处理 Oracle 函数
            if ("TO_DATE".equalsIgnoreCase(functionName) && params != null && params.size() >= 2) {
                String dateStr = params.get(0).toString();
                String oracleFormat = params.get(1).toString().replaceAll("['\"]", "");
                String mysqlFormat = convertDateFormat(oracleFormat);
                return "STR_TO_DATE(" + dateStr + ", " + mysqlFormat + ")";
            } else if ("SYSDATE".equalsIgnoreCase(functionName)) {
                return "NOW()";
            } else if ("SYSTIMESTAMP".equalsIgnoreCase(functionName)) {
                return "NOW()";
            } else if ("NVL".equalsIgnoreCase(functionName) && params != null && params.size() == 2) {
                return "IFNULL(" + convertExpression(params.get(0)) + ", " + convertExpression(params.get(1)) + ")";
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
                return "NOW()";
            }
            return cleanIdentifier(colName);
        }

        // 处理 IntervalExpression（INTERVAL '365' DAY）
        try {
            // 检查是否是 IntervalExpression
            if (expression.getClass().getSimpleName().contains("Interval")) {
                String intervalStr = expression.toString();
                // 使用 convertOracleFunctions 处理 INTERVAL 转换（去掉引号）
                intervalStr = convertOracleFunctions(intervalStr);
                return intervalStr;
            }
        } catch (Exception ignore) {}

        // 处理其他表达式类型...
        String exprStr = expression.toString();
        // 使用 convertOracleFunctions 处理 SYSDATE 和 INTERVAL
        exprStr = convertOracleFunctions(exprStr);
        return exprStr;
    }

    // 辅助方法：转换||连接符为CONCAT函数（Oracle -> MySQL）
    private String convertConcatOperator(String sql) {
        if (sql == null || sql.isEmpty()) return sql;
        
        // 匹配 || 操作符，但要小心处理字符串中的 ||
        // 使用正则表达式匹配 || 前后的表达式
        // 这是一个简化版本，复杂情况可能需要在AST层面处理
        Pattern concatPattern = Pattern.compile("([^|]+)\\|\\|([^|]+)");
        Matcher matcher = concatPattern.matcher(sql);
        
        if (!matcher.find()) {
            return sql; // 没有||操作符
        }
        
        // 递归处理多个||连接
        String result = sql;
        while (matcher.find() || concatPattern.matcher(result).find()) {
            // 找到所有连续的||连接
            // 使用更精确的方法：找到||，然后向前向后查找表达式边界
            StringBuilder sb = new StringBuilder();
            int lastEnd = 0;
            boolean inString = false;
            char stringChar = 0;
            int parenDepth = 0;
            
            for (int i = 0; i < result.length() - 1; i++) {
                char ch = result.charAt(i);
                char next = result.charAt(i + 1);
                
                if (!inString && (ch == '\'' || ch == '"')) {
                    inString = true;
                    stringChar = ch;
                    sb.append(ch);
                } else if (inString && ch == stringChar && (i == 0 || result.charAt(i - 1) != '\\')) {
                    inString = false;
                    sb.append(ch);
                } else if (!inString && ch == '(') {
                    parenDepth++;
                    sb.append(ch);
                } else if (!inString && ch == ')') {
                    parenDepth--;
                    sb.append(ch);
                } else if (!inString && ch == '|' && next == '|' && parenDepth == 0) {
                    // 找到||操作符
                    String leftPart = sb.toString().trim();
                    // 查找右侧表达式（直到下一个||或表达式结束）
                    StringBuilder rightPart = new StringBuilder();
                    int j = i + 2;
                    while (j < result.length()) {
                        char rc = result.charAt(j);
                        if (!inString && (rc == '\'' || rc == '"')) {
                            inString = true;
                            stringChar = rc;
                            rightPart.append(rc);
                        } else if (inString && rc == stringChar && (j == 0 || result.charAt(j - 1) != '\\')) {
                            inString = false;
                            rightPart.append(rc);
                        } else if (!inString && rc == '(') {
                            parenDepth++;
                            rightPart.append(rc);
                        } else if (!inString && rc == ')') {
                            parenDepth--;
                            rightPart.append(rc);
                        } else if (!inString && rc == '|' && j + 1 < result.length() && result.charAt(j + 1) == '|' && parenDepth == 0) {
                            // 遇到下一个||，停止
                            break;
                        } else if (!inString && (rc == ',' || rc == ';' || rc == ')' || rc == ' ') && parenDepth == 0 && rightPart.length() > 0) {
                            // 可能是表达式边界
                            if (rc == ' ' && j + 1 < result.length() && result.charAt(j + 1) != '|') {
                                // 空格后不是||，可能是表达式结束
                                break;
                            } else if (rc != ' ') {
                                break;
                            }
                        } else {
                            rightPart.append(rc);
                        }
                        j++;
                    }
                    
                    String right = rightPart.toString().trim();
                    // 检查left和right是否已经是CONCAT函数的一部分
                    if (!leftPart.contains("CONCAT(") && !right.contains("CONCAT(")) {
                        sb.setLength(0);
                        sb.append("CONCAT(").append(leftPart).append(", ").append(right).append(")");
                        // 继续处理剩余的字符串
                        result = sb.toString() + result.substring(j);
                        break;
                    } else {
                        sb.append(ch);
                    }
                } else {
                    sb.append(ch);
                }
            }
            
            if (sb.length() > 0 && !sb.toString().equals(result)) {
                result = sb.toString();
            } else {
                break;
            }
        }
        
        return result;
    }

    // 工具方法：转换 Oracle 函数为 MySQL 函数
    private String convertOracleFunctions(String sql) {
        if (sql == null) return "";
        String result = sql;
        
        // 先转换||连接符为CONCAT函数
        // 注意：这是一个简化版本，复杂嵌套可能需要AST处理
        // 简单情况：表达式 || 表达式
        result = result.replaceAll("([^|\\s]+)\\s*\\|\\|\\s*([^|\\s]+)", "CONCAT($1, $2)");
        
        // SYSDATE -> NOW()
        result = result.replaceAll("(?i)\\bSYSDATE\\b", "NOW()");
        // SYSTIMESTAMP -> NOW()
        result = result.replaceAll("(?i)\\bSYSTIMESTAMP\\b", "NOW()");
        // NVL -> IFNULL
        result = result.replaceAll("(?i)\\bNVL\\s*\\(", "IFNULL(");
        
        // INTERVAL 转换（Oracle: INTERVAL '365' DAY，MySQL: INTERVAL 365 DAY）
        // 去掉 INTERVAL 中数值的引号
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+YEAR", "INTERVAL $1 YEAR");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+MONTH", "INTERVAL $1 MONTH");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+DAY", "INTERVAL $1 DAY");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+HOUR", "INTERVAL $1 HOUR");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+MINUTE", "INTERVAL $1 MINUTE");
        result = result.replaceAll("(?i)INTERVAL\\s+'([^']+)'\\s+SECOND", "INTERVAL $1 SECOND");
        
        return result;
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