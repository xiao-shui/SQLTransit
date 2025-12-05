package org.example.SqlTransitAI.tool;

import net.sf.jsqlparser.statement.create.table.ColumnDefinition;
import net.sf.jsqlparser.statement.create.table.CreateTable;
import net.sf.jsqlparser.statement.create.index.CreateIndex;
import net.sf.jsqlparser.statement.insert.Insert;
import net.sf.jsqlparser.statement.StatementVisitorAdapter;
import net.sf.jsqlparser.schema.Column;
import net.sf.jsqlparser.statement.delete.Delete;
import net.sf.jsqlparser.statement.update.Update;
import net.sf.jsqlparser.expression.Expression;

import java.util.List;
import java.util.stream.Collectors;

public class MysqlToOracleVisitor extends StatementVisitorAdapter {
    private StringBuilder oracleSql = new StringBuilder();

    // 工具方法：将表达式SQL里的 true/false 替换为 1/0 (忽略字符串字面量)
    private String replaceBooleanLiterals(String sql) {
        // 1. 排除单引号字符串内的 true/false 替换
        StringBuilder sb = new StringBuilder();
        boolean inString = false;
        int len = sql.length();

        for (int i = 0; i < len; i++) {
            char ch = sql.charAt(i);
            if (ch == '\'') {
                sb.append(ch);
                // 检查是否是转义的单引号
                if (i + 1 < len && sql.charAt(i + 1) == '\'') {
                    // 双单引号，转义
                    sb.append('\'');
                    i++;
                    continue;
                }
                inString = !inString;
                continue;
            }

            if (!inString) {
                // 检查 true/false 单词（只替换完整词且区分大小写）
                if ((i + 4 <= len && sql.substring(i, i + 4).equalsIgnoreCase("true")) &&
                        (i + 4 == len || !Character.isLetterOrDigit(sql.charAt(i + 4))) &&
                        (i == 0 || !Character.isLetterOrDigit(sql.charAt(i - 1)))) {
                    sb.append("Y");
                    i += 3;
                    continue;
                }
                if ((i + 5 <= len && sql.substring(i, i + 5).equalsIgnoreCase("false")) &&
                        (i + 5 == len || !Character.isLetterOrDigit(sql.charAt(i + 5))) &&
                        (i == 0 || !Character.isLetterOrDigit(sql.charAt(i - 1)))) {
                    sb.append("N");
                    i += 4;
                    continue;
                }
            }

            sb.append(ch);
        }

        return sb.toString();
    }

    // 处理 CREATE TABLE（核心差异：自增、字段类型、默认值、字段名大写，无需加引号，UNIQUE/NOT NULL约束处理）
    @Override
    public void visit(CreateTable createTable) {
        String tableName = createTable.getTable().getName().toUpperCase();
        String tableNameLower = createTable.getTable().getName().toLowerCase();
        oracleSql.append("CREATE TABLE ").append(tableName).append(" (\n");

        List<ColumnDefinition> columns = createTable.getColumnDefinitions();

        // 收集需要在末尾添加的unique约束
        StringBuilder uniqueConstraints = new StringBuilder();

        for (int i = 0; i < columns.size(); i++) {
            ColumnDefinition col = columns.get(i);

            if (i != 0) {
                oracleSql.append(",\n");
            }

            String colName = col.getColumnName().toUpperCase();
            String colNameLower = col.getColumnName().toLowerCase();
            String colType = convertColumnType(col.getColDataType().getDataType(), col.getColDataType().getArgumentsStringList());

            // JSQLParser 4.x 以后没有 getColumnSpecStrings，使用 getColumnSpecs（通常是 List<?> 或 List<Object>）
            List<?> specStrings = null;
            try {
                specStrings = (List<?>) col.getClass().getMethod("getColumnSpecs").invoke(col);
            } catch (Exception e) {
                // 如果没有此方法或调用异常，则解析特殊属性时跳过
            }

            boolean isAutoIncrement = false;
            boolean isPrimaryKey = false;
            boolean isNotNull = false;
            boolean isUnique = false;
            String defaultValStr = null;

            if (specStrings != null) {
                for (int j = 0; j < specStrings.size(); j++) {
                    Object obj = specStrings.get(j);
                    if (obj instanceof String) {
                        String s = ((String) obj).toUpperCase();
                        if ("AUTO_INCREMENT".equals(s)) {
                            isAutoIncrement = true;
                        }
                        if ("PRIMARY".equals(s) && (j + 1 < specStrings.size())) {
                            Object nextObj = specStrings.get(j + 1);
                            if (nextObj instanceof String
                                    && "KEY".equalsIgnoreCase(((String) nextObj))) {
                                isPrimaryKey = true;
                            }
                        }
                        if ("NOT".equals(s) && (j + 1 < specStrings.size())) {
                            Object nextObj = specStrings.get(j + 1);
                            if (nextObj instanceof String
                                    && "NULL".equalsIgnoreCase(((String) nextObj))) {
                                isNotNull = true;
                            }
                        }
                        if ("DEFAULT".equals(s) && (j + 1 < specStrings.size())) {
                            Object nextObj = specStrings.get(j + 1);
                            if (nextObj instanceof String) {
                                defaultValStr = (String) nextObj;
                            }
                        }
                        if ("UNIQUE".equals(s)) {
                            isUnique = true;
                        }
                    }
                }
            }

            // 字段名无需加双引号，只需大写即可
            oracleSql.append("    ").append(colName).append(" ").append(colType);

            // identity/auto_increment转Oracle方式
            if (isAutoIncrement) {
                oracleSql.append(" GENERATED BY DEFAULT AS IDENTITY");
            }

            // 默认值支持
            if (defaultValStr != null) {
                if (defaultValStr.toUpperCase().contains("CURRENT_TIMESTAMP")) {
                    // DATETIME/DATE的CURRENT_TIMESTAMP
                    oracleSql.append(" DEFAULT SYSDATE");
                } else if (colType.equalsIgnoreCase("VARCHAR2(1)") &&
                        (defaultValStr.equalsIgnoreCase("true") || defaultValStr.equalsIgnoreCase("false"))) {
                    // 对于bool/boolean类型（Oracle用VARCHAR2(1)），用'Y'或'N'
                    if (defaultValStr.equalsIgnoreCase("true")) {
                        oracleSql.append(" DEFAULT Y");
                    } else {
                        oracleSql.append(" DEFAULT N");
                    }
                } else {
                    oracleSql.append(" DEFAULT ").append(defaultValStr);
                }
            } else {
                // 对于bool/boolean字段,给默认 'Y'
                if (colType.equalsIgnoreCase("VARCHAR2(1)")) {
                    oracleSql.append(" DEFAULT 'Y'");
                }
            }

            // NOT NULL（一般不用加在自增主键上）
            if (isNotNull && !(isPrimaryKey && isAutoIncrement)) {
                oracleSql.append(" NOT NULL");
            }

            // PRIMARY KEY
            if (isPrimaryKey) {
                oracleSql.append(" PRIMARY KEY");
            }

            // UNIQUE 约束移到表级，确实 unique+not null都要体现
            if (isUnique) {
                if (uniqueConstraints.length() > 0) {
                    uniqueConstraints.append(",\n");
                }
                uniqueConstraints.append("    CONSTRAINT uk_")
                        .append(tableNameLower)
                        .append("_")
                        .append(colNameLower)
                        .append(" UNIQUE(")
                        .append(colName)
                        .append(")");
            }
        }

        // 添加表级unique约束
        if (uniqueConstraints.length() > 0) {
            oracleSql.append(",\n");
            oracleSql.append(uniqueConstraints);
        }

        oracleSql.append("\n);\n\n");
    }

    // 处理索引 CREATE INDEX、UNIQUE INDEX 语句转换
    @Override
    public void visit(CreateIndex createIndex) {
        String indexName = createIndex.getIndex().getName().toUpperCase();
        String tableName = createIndex.getTable().getName().toUpperCase();
        boolean isUnique = false;

        // 兼容 MySQL/JSQLParser 的 UNIQUE 索引类型，通过 SQL 解析 type 字符串和索引名是否以 'UNIQUE_' 开头
        // 注意：JSQLParser 不同版本 CreateIndex 结构变动较大，不要直接调用 getType/isUnique
        String idxAttrString = createIndex.toString().toUpperCase();
        // 最保险判断法：SQL片段是否带有 'CREATE UNIQUE INDEX ...'
        // 或者索引名本身带 UNIQUE 字样
        if (idxAttrString.contains("CREATE UNIQUE INDEX")
                || (indexName != null && indexName.startsWith("UNIQUE_"))) {
            isUnique = true;
        }

        // 不能直接使用 getColumnsNames 方法，使用反射或直接访问字段
        List<?> columnsList = null;
        try {
            // 1. 尝试 getColumns (标准API 是 getColumns())
            columnsList = (List<?>) createIndex.getClass().getMethod("getColumns").invoke(createIndex);
        } catch (Exception e) {
            try {
                // 2. 尝试直接取 public 字段
                columnsList = (List<?>) createIndex.getClass().getField("columnsNames").get(createIndex);
            } catch (Exception ex) {
                // 失败则为空
                columnsList = null;
            }
        }
        String columns = "";
        if (columnsList != null && !columnsList.isEmpty()) {
            // 兼容可能的类型：Column, String
            columns = columnsList.stream()
                    .map(obj -> {
                        if (obj instanceof Column) {
                            return ((Column) obj).getColumnName().toUpperCase();
                        } else {
                            return obj.toString().toUpperCase();
                        }
                    })
                    .collect(Collectors.joining(", "));
        }

        oracleSql.append("CREATE");
        if (isUnique) {
            oracleSql.append(" UNIQUE");
        }
        oracleSql.append(" INDEX ").append(indexName);
        oracleSql.append(" ON ").append(tableName);
        oracleSql.append(" (").append(columns).append(");\n\n");
    }

    // 处理 INSERT（表名字段名均需加双引号，且大写，日期函数替换）
    @Override
    public void visit(Insert insert) {
        // 表名去掉MySQL反引号和单引号只保留大写
        String tableNameRaw = insert.getTable().getName();
        String tableName = tableNameRaw.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
        oracleSql.append("INSERT INTO ").append(tableName);

        List<Column> columns = insert.getColumns();
        if (columns != null && !columns.isEmpty()) {
            oracleSql.append("(");
            for (int i = 0; i < columns.size(); i++) {
                // 字段处理：清除包裹的反引号和单引号，只剩大写
                String rawColName = columns.get(i).getColumnName();
                String colName = rawColName.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
                oracleSql.append(colName);
                if (i < columns.size() - 1) oracleSql.append(", ");
            }
            oracleSql.append(")");
        }

        // values部分直接取原始SQL并智能替换
        String insertStr = insert.toString();
        int valuesIdx = insertStr.toUpperCase().indexOf("VALUES");
        String valuesPart = "";
        if (valuesIdx != -1) {
            valuesPart = insertStr.substring(valuesIdx + 6)
                    .replace("CURRENT_TIMESTAMP", "SYSDATE");
            valuesPart = replaceBooleanLiterals(valuesPart);
        }
        oracleSql.append(" VALUES").append(valuesPart).append(";\n\n");
    }

    // 新增：处理 DELETE
    @Override
    public void visit(Delete delete) {
        // 表名去掉MySQL的`和'只保留大写
        String tableNameRaw = delete.getTable().getName();
        String tableName = tableNameRaw.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
        oracleSql.append("DELETE FROM ").append(tableName);
        // WHERE 条件
        Expression where = delete.getWhere();
        if (where != null) {
            // 尝试保留原生SQL语句的where部份，替换CURRENT_TIMESTAMP、true/false
            String whereStr = where.toString().replace("CURRENT_TIMESTAMP", "SYSDATE");
            whereStr = replaceBooleanLiterals(whereStr);
            oracleSql.append(" WHERE ").append(whereStr);
        }
        oracleSql.append(";\n\n");
    }

    // 新增：处理 UPDATE
    @Override
    public void visit(Update update) {
        // 表名去掉MySQL的`和'只保留大写
        String tableNameRaw = update.getTable().getName();
        String tableName = tableNameRaw.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
        oracleSql.append("UPDATE ").append(tableName).append(" SET ");

        List<Column> columns = update.getColumns();
        List<Expression> expressions = update.getExpressions();
        for (int i = 0; i < columns.size(); i++) {
            String rawColName = columns.get(i).getColumnName();
            String colName = rawColName.replaceAll("^[`'\"]+|[`'\"]+$", "").toUpperCase();
            String valueExpr = expressions.get(i).toString().replace("CURRENT_TIMESTAMP", "SYSDATE");
            valueExpr = replaceBooleanLiterals(valueExpr);
            oracleSql.append(colName).append("=").append(valueExpr);
            if (i < columns.size() - 1) {
                oracleSql.append(", ");
            }
        }

        Expression where = update.getWhere();
        if (where != null) {
            String whereStr = where.toString().replace("CURRENT_TIMESTAMP", "SYSDATE");
            whereStr = replaceBooleanLiterals(whereStr);
            oracleSql.append(" WHERE ").append(whereStr);
        }
        oracleSql.append(";\n\n");
    }

    // 字段类型映射：带长度支持
    private String convertColumnType(String mysqlType, List<?> args) {
        String type = mysqlType.toUpperCase();
        switch (type) {
            case "INT":
                return "NUMBER";
            case "VARCHAR":
                if (args != null && !args.isEmpty()) {
                    return "VARCHAR2(" + args.get(0) + ")";
                } else {
                    return "VARCHAR2";
                }
            case "DATETIME":
                return "DATE";
            case "TIMESTAMP":
                return "DATE";
            case "BIGINT":
                return "NUMBER(20)";
            case "TINYINT":
                return "NUMBER(3)";
            case "BOOLEAN":
            case "BOOL":
                return "VARCHAR2(1)";
            default:
                // 若类型带参数
                if (args != null && !args.isEmpty()) {
                    return type + "(" + args.get(0) + ")";
                }
                return type;
        }
    }

    // 获取转换后的 Oracle 脚本
    public String getOracleSql() {
        return oracleSql.toString();
    }
}
