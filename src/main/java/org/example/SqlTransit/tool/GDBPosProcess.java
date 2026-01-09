package org.example.SqlTransit.tool;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

/**
 * GoldenDB SQL 后处理类
 * 为转换后的 GoldenDB 脚本添加缺失的分片配置
 */
public class GDBPosProcess {

    /**
     * 后处理 GoldenDB SQL，添加缺失的分片配置
     *
     * @param sql 转换后的 GoldenDB SQL
     * @return 添加分片配置后的 SQL
     */
    public static String postprocess(String sql) {
        if (sql == null || sql.trim().isEmpty()) {
            return sql;
        }

        String result = sql;

        // 为 CREATE TABLE 语句添加分片配置（如果缺失）
        result = addShardingConfig(result);

        return result;
    }

    /**
     * 为 CREATE TABLE 语句添加分片配置（如果缺失）
     * 分片配置格式：DISTRIBUTED BY HASH(主键列);
     * 应该添加在表定义的末尾，即 ENGINE=... 或 COMMENT='...' 之后
     */
    private static String addShardingConfig(String sql) {
        // 使用括号计数来找到表定义结束的最后一个 )
        StringBuffer result = new StringBuffer();
        Pattern createTablePattern = Pattern.compile(
                "(?i)CREATE\\s+TABLE",
                Pattern.CASE_INSENSITIVE);

        int lastIndex = 0;
        Matcher createTableMatcher = createTablePattern.matcher(sql);

        while (createTableMatcher.find()) {
            int startPos = createTableMatcher.start();
            result.append(sql.substring(lastIndex, startPos));

            // 从 CREATE TABLE 开始，找到列定义结束的最后一个 )
            int pos = createTableMatcher.end();
            int parenCount = 0;
            int tableDefEnd = -1;
            boolean inQuotes = false;
            char quoteChar = 0;

            // 跳过表名部分，找到第一个 (
            while (pos < sql.length()) {
                char c = sql.charAt(pos);
                if (!inQuotes && (c == '"' || c == '\'' || c == '`')) {
                    inQuotes = true;
                    quoteChar = c;
                } else if (inQuotes && c == quoteChar) {
                    inQuotes = false;
                } else if (!inQuotes && c == '(') {
                    parenCount = 1;
                    pos++;
                    break;
                }
                pos++;
            }

            // 找到匹配的最后一个 )
            while (pos < sql.length() && parenCount > 0) {
                char c = sql.charAt(pos);
                if (!inQuotes && (c == '"' || c == '\'' || c == '`')) {
                    inQuotes = true;
                    quoteChar = c;
                } else if (inQuotes && c == quoteChar) {
                    inQuotes = false;
                } else if (!inQuotes) {
                    if (c == '(') {
                        parenCount++;
                    } else if (c == ')') {
                        parenCount--;
                        if (parenCount == 0) {
                            tableDefEnd = pos;
                            break;
                        }
                    }
                }
                pos++;
            }

            if (tableDefEnd > 0) {
                // 找到表定义结束位置，查找分号位置
                int semicolonPos = sql.indexOf(';', tableDefEnd + 1);
                if (semicolonPos > 0) {
                    String tableDef = sql.substring(startPos, tableDefEnd + 1);
                    String afterTableDef = sql.substring(tableDefEnd + 1, semicolonPos);

                    // 检查是否已有 DISTRIBUTED BY 配置
                    boolean hasDistributed = afterTableDef.trim().toUpperCase().contains("DISTRIBUTED BY");

                    if (!hasDistributed) {
                        // 没有分片配置，从表定义中提取主键并添加配置
                        String primaryKey = extractPrimaryKey(tableDef);
                        String shardingClause = buildShardingClause(primaryKey);
                        result.append(tableDef).append(afterTableDef).append(shardingClause).append(";");
                    } else {
                        // 已有分片配置，保持不变
                        result.append(sql.substring(startPos, semicolonPos + 1));
                    }
                    lastIndex = semicolonPos + 1;
                } else {
                    // 没有找到分号，保持原样并停止处理
                    result.append(sql.substring(startPos));
                    lastIndex = sql.length();
                    break; // 停止处理后续的 CREATE TABLE 语句
                }
            } else {
                // 没有找到匹配的 )，保持原样并停止处理
                result.append(sql.substring(startPos));
                lastIndex = sql.length();
                break; // 停止处理后续的 CREATE TABLE 语句
            }
        }

        result.append(sql.substring(lastIndex));
        return result.toString();
    }

    /**
     * 从 CREATE TABLE 语句中提取主键列
     * 支持三种格式：
     * 1. 列级主键：`column_name` ... PRIMARY KEY
     * 2. 表级主键（带 CONSTRAINT）：CONSTRAINT ... PRIMARY KEY (`column1`, `column2`)
     * 3. 表级主键（不带 CONSTRAINT）：PRIMARY KEY (`column1`, `column2`)
     *
     * @param tableDef CREATE TABLE 的列定义部分（从 CREATE TABLE 到最后一个 )）
     * @return 主键列名，多个列用逗号分隔，如果没有主键返回 null
     */
    private static String extractPrimaryKey(String tableDef) {
        // 找到列定义部分的开始位置（第一个左括号之后）
        int firstParenPos = tableDef.indexOf('(');
        if (firstParenPos == -1) {
            return null;
        }

        // 只从列定义部分（括号内）提取主键，避免匹配到表名
        String columnDefPart = tableDef.substring(firstParenPos);

        // 先尝试提取表级主键约束（带 CONSTRAINT）：CONSTRAINT ... PRIMARY KEY (columns)
        Pattern tablePkWithConstraintPattern = Pattern.compile(
                "(?i)CONSTRAINT\\s+[^\\s(]+\\s+PRIMARY\\s+KEY\\s*\\(([^)]+)\\)",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher tablePkWithConstraintMatcher = tablePkWithConstraintPattern.matcher(columnDefPart);

        if (tablePkWithConstraintMatcher.find()) {
            String pkColumns = tablePkWithConstraintMatcher.group(1);
            String cleaned = cleanPrimaryKeyColumns(pkColumns);
            if (cleaned != null && !cleaned.isEmpty()) {
                return cleaned;
            }
        }

        // 再尝试提取表级主键约束（不带 CONSTRAINT）：PRIMARY KEY (columns)
        // 使用更精确的匹配，确保匹配的是列定义中的 PRIMARY KEY，而不是表名
        // 匹配模式：PRIMARY KEY 前面应该是逗号、换行或空格，后面是括号和列名
        Pattern tablePkPattern = Pattern.compile(
                "(?i)(?:^|[,;\\s]+)PRIMARY\\s+KEY\\s*\\(([^)]+)\\)",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL | Pattern.MULTILINE);
        Matcher tablePkMatcher = tablePkPattern.matcher(columnDefPart);

        if (tablePkMatcher.find()) {
            String pkColumns = tablePkMatcher.group(1);
            // 验证提取的内容是列名格式（不能是表名）
            // 表名通常不包含在列定义的 PRIMARY KEY 括号内
            String cleaned = cleanPrimaryKeyColumns(pkColumns);
            if (cleaned != null && !cleaned.isEmpty()) {
                // 进一步验证：确保提取的内容看起来像列名（包含引号或有效的标识符）
                // 如果提取的内容看起来不像列名（比如是完整的表名），则跳过
                return cleaned;
            }
        }

        // 最后尝试提取列级主键：`column_name` ... PRIMARY KEY
        // 匹配模式：列定义中包含 PRIMARY KEY 的列
        Pattern columnPkPattern = Pattern.compile(
                "(?i)`([^`]+)`[^,)]*?PRIMARY\\s+KEY",
                Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
        Matcher columnPkMatcher = columnPkPattern.matcher(columnDefPart);

        if (columnPkMatcher.find()) {
            String columnName = columnPkMatcher.group(1);
            // 确保提取的不是表名（表名通常在 CREATE TABLE 之后，不在列定义中）
            if (columnName != null && !columnName.trim().isEmpty()) {
                return "`" + columnName + "`";
            }
        }

        // 如果没有找到主键，返回 null
        return null;
    }

    /**
     * 清理主键列字符串，确保格式正确
     * 输入可能是：`col1`, `col2` 或 col1, col2
     * 输出统一为：`col1`, `col2`
     */
    private static String cleanPrimaryKeyColumns(String columns) {
        if (columns == null || columns.trim().isEmpty()) {
            return null;
        }

        String[] colArray = columns.split(",");
        StringBuilder result = new StringBuilder();

        for (int i = 0; i < colArray.length; i++) {
            String col = colArray[i].trim();
            // 移除所有引号
            col = col.replaceAll("[`'\"]", "");
            // 重新添加反引号
            if (!col.isEmpty()) {
                if (i > 0) {
                    result.append(", ");
                }
                result.append("`").append(col).append("`");
            }
        }

        return result.length() > 0 ? result.toString() : null;
    }

    /**
     * 构建分片配置子句
     * 格式：DISTRIBUTED BY HASH(主键列)
     * 如果没有主键，使用 DUPLICATE 模式
     *
     * @param primaryKey 主键列，多个列用逗号分隔，如果没有主键为 null
     * @return 分片配置子句
     */
    private static String buildShardingClause(String primaryKey) {
        if (primaryKey != null && !primaryKey.trim().isEmpty()) {
            // 有主键，使用 HASH 分片
            return " DISTRIBUTED BY HASH(" + primaryKey + ")";
        } else {
            // 没有主键，使用 DUPLICATE 模式（全量复制）
            return " ";
        }
    }

    /**
     * 批量后处理多条 SQL 语句
     *
     * @param sqls SQL 语句数组
     * @return 处理后的 SQL 语句数组
     */
    public static String[] postprocessBatch(String[] sqls) {
        if (sqls == null) {
            return null;
        }
        String[] results = new String[sqls.length];
        for (int i = 0; i < sqls.length; i++) {
            results[i] = postprocess(sqls[i]);
        }
        return results;
    }
}
