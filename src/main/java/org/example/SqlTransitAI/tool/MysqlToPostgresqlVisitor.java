package org.example.SqlTransitAI.tool;

import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.expression.Expression;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;

import java.util.*;
import java.util.stream.Collectors;

/**
 * 将MySQL解析出的AST转为PostgreSQL方言
 */
public class MysqlToPostgresqlVisitor extends StatementVisitorAdapter {
    private final StringBuilder pgSql = new StringBuilder();

    // 工具方法：清理标识符（去除MySQL引号，并小写）
    private String cleanIdentifier(String name) {
        if (name == null) return null;
        return name.replaceAll("^[`'\"]+|[`'\"]+$", "").toLowerCase();
    }

    // 工具方法：MySQL类型 → PostgreSQL类型
    private String mysqlTypeToPgType(String mysqlType) {
        String origType = mysqlType.toLowerCase();
        if (origType.startsWith("int(") || origType.equals("int") || origType.startsWith("integer")) {
            return "integer";
        }
        if (origType.startsWith("tinyint(1)")) {
            return "boolean";
        }
        if (origType.startsWith("tinyint")) {
            return "smallint";
        }
        if (origType.startsWith("bigint")) {
            return "bigint";
        }
        if (origType.startsWith("varchar")) {
            return origType.replace("varchar", "varchar");
        }
        if (origType.startsWith("datetime") || origType.startsWith("timestamp")) {
            return "timestamp";
        }
        if (origType.startsWith("date")) {
            return "date";
        }
        if (origType.startsWith("double")) {
            return "double precision";
        }
        if (origType.startsWith("float")) {
            return "real";
        }
        if (origType.startsWith("text")) {
            return "text";
        }
        if (origType.startsWith("char")) {
            return origType.replace("char", "char");
        }
        if (origType.startsWith("decimal")) {
            return origType.replace("decimal", "numeric");
        }
        // fallback
        return mysqlType;
    }

    /**
     * 处理 CREATE TABLE
     */
    @Override
    public void visit(CreateTable createTable) {
        String tableName = cleanIdentifier(createTable.getTable().getName());
        pgSql.append("CREATE TABLE ").append(tableName).append(" (\n");
        List<String> colStrs = new ArrayList<>();
        List<String> pkCols = new ArrayList<>();
        List<ColumnDefinition> colDefs = createTable.getColumnDefinitions();

        if (colDefs != null) {
            for (ColumnDefinition colDef : colDefs) {
                String colName = cleanIdentifier(colDef.getColumnName());
                String colType = mysqlTypeToPgType(colDef.getColDataType().toString());
                StringBuilder colSb = new StringBuilder(colName + " " + colType);

                // 由于无法直接获得 getColumnSpecStrings 方法，手动分析 colDef 的 toString() 结果
                // 常见的自增/not null/unique/default等
                boolean isAutoInc = false;
                String colDefStr = colDef.toString().toLowerCase();
                // 判断自增
                if (colDefStr.contains("auto_increment")) {
                    isAutoInc = true;
                }
                // 判断 not null
                if (colDefStr.contains("not null")) {
                    colSb.append(" NOT NULL");
                }
                // 判断 unique
                if (colDefStr.contains("unique")) {
                    colSb.append(" UNIQUE");
                }
                // 默认值, 尝试正则匹配 default xxx
                int defIdx = colDefStr.indexOf("default");
                if (defIdx != -1) {
                    int afterDef = defIdx + "default".length();
                    // 寻找 default 后第一个非空字符
                    while (afterDef < colDefStr.length() && Character.isWhitespace(colDefStr.charAt(afterDef))) {
                        afterDef++;
                    }
                    // 取到空格/逗号或闭括号/字符串末尾为止
                    int endPos = afterDef;
                    boolean inString = false;
                    while (endPos < colDefStr.length()) {
                        char c = colDefStr.charAt(endPos);
                        if (c == '\'' || c == '"') inString = !inString;
                        if (!inString && (Character.isWhitespace(c) || c == ',' || c == ')')) break;
                        endPos++;
                    }
                    String defValue = colDefStr.substring(afterDef, endPos);
                    if ("current_timestamp".equals(defValue.trim())) {
                        colSb.append(" DEFAULT CURRENT_TIMESTAMP");
                    } else if (!defValue.isEmpty()) {
                        colSb.append(" DEFAULT ").append(defValue.trim());
                    }
                }

                // PostgreSQL序列主键
                if (isAutoInc) {
                    if (colType.equals("bigint")) {
                        colSb = new StringBuilder(colName + " bigserial");
                    } else {
                        colSb = new StringBuilder(colName + " serial");
                    }
                }

                colStrs.add(colSb.toString());
            }
        }

        // 主键，仍然从 getIndexes 获取字段名字符串
        if (createTable.getIndexes() != null) {
            for (Object idxObj : createTable.getIndexes()) {
                // hack: 只处理primary key
                String idxStr = idxObj.toString().toLowerCase();
                if (idxStr.startsWith("primary key")) {
                    int l = idxStr.indexOf("("), r = idxStr.indexOf(")");
                    if (l > 0 && r > l) {
                        String pkIn = idxStr.substring(l + 1, r);
                        pkCols.addAll(Arrays.asList(pkIn.replaceAll("[`'\"]", "").split("\\s*,\\s*")));
                    }
                }
            }
        }
        if (!pkCols.isEmpty()) {
            colStrs.add("PRIMARY KEY (" + pkCols.stream().map(String::trim).map(this::cleanIdentifier).collect(Collectors.joining(", ")) + ")");
        }

        pgSql.append(String.join(",\n", colStrs));
        pgSql.append("\n);\n\n");
    }

    /**
     * 处理 CREATE INDEX
     */
    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = cleanIdentifier(createIndex.getIndex().getName());
        String tableName = cleanIdentifier(createIndex.getTable().getName());
        // 无法直接获得 getType 方法，改用 toString 检查字符串是否包含 unique
        boolean isUnique = createIndex.toString().toLowerCase().contains("unique");
        List<String> columns = new ArrayList<>();
        // 无法直接获得 getColumnsNames/getColumns，尝试从 toString() 解析字段
        // 一般格式：CREATE [UNIQUE] INDEX idx_name ON table (col1, col2...)
        String idxStr = createIndex.toString().toLowerCase();
        int lIdx = idxStr.indexOf("("), rIdx = idxStr.indexOf(")");
        if (lIdx > 0 && rIdx > lIdx) {
            String colsPart = idxStr.substring(lIdx + 1, rIdx);
            for (String col : colsPart.split(",")) {
                columns.add(cleanIdentifier(col.trim()));
            }
        }

        pgSql.append("CREATE");
        if (isUnique) pgSql.append(" UNIQUE");
        pgSql.append(" INDEX ");
        pgSql.append(indexName)
                .append(" ON ")
                .append(tableName)
                .append(" (").append(String.join(", ", columns)).append(");\n\n");
    }

    /**
     * 处理 INSERT
     */
    @Override
    public void visit(Insert insert) {
        String tableName = cleanIdentifier(insert.getTable().getName());
        pgSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            pgSql.append("(");
            for (int i = 0; i < columns.size(); i++) {
                String colName = cleanIdentifier(columns.get(i).getColumnName());
                pgSql.append(colName);
                if (i < columns.size() - 1) pgSql.append(", ");
            }
            pgSql.append(")");
        }
        // values部分直接取toString, 可能没法逐一AST级别替换
        String insertStr = insert.toString();
        int valuesIdx = insertStr.toUpperCase().indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = insertStr.substring(valuesIdx + 6);
            // 替换MySQL自带的CURRENT_TIMESTAMP为Postgres
            valuesPart = valuesPart.replace("CURRENT_TIMESTAMP", "CURRENT_TIMESTAMP");
        }
        pgSql.append(" VALUES").append(valuesPart).append(";\n\n");
    }

    /**
     * 处理 UPDATE
     */
    @Override
    public void visit(Update update) {
        String tableName = cleanIdentifier(update.getTable().getName());
        pgSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> cols = update.getColumns();
        List<Expression> exprs = update.getExpressions();
        for (int i = 0; i < cols.size(); i++) {
            String colName = cleanIdentifier(cols.get(i).getColumnName());
            String valueExpr = exprs.get(i).toString();
            valueExpr = valueExpr.replace("CURRENT_TIMESTAMP", "CURRENT_TIMESTAMP");
            pgSql.append(colName).append("=").append(valueExpr);
            if (i < cols.size() - 1) pgSql.append(", ");
        }

        if (update.getWhere() != null) {
            pgSql.append(" WHERE ").append(update.getWhere().toString());
        }
        pgSql.append(";\n\n");
    }

    /**
     * 处理 DELETE
     */
    @Override
    public void visit(Delete delete) {
        String tableName = cleanIdentifier(delete.getTable().getName());
        pgSql.append("DELETE FROM ").append(tableName);
        if (delete.getWhere() != null) {
            pgSql.append(" WHERE ").append(delete.getWhere().toString());
        }
        pgSql.append(";\n\n");
    }

    public String getPostgresqlSql() {
        return pgSql.toString();
    }
}
