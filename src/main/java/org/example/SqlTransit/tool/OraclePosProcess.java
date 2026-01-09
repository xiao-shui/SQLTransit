package org.example.SqlTransit.tool;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

/**
 * Oracle SQL 后处理类
 * 为转换后的 Oracle 脚本添加缺失的存储配置
 */
public class OraclePosProcess {
    
    // 默认表空间名称（可以根据需要修改）
    private static final String DEFAULT_TABLESPACE = "DISPATCH_TEST";
    
    /**
     * 后处理 Oracle SQL，添加缺失的存储配置
     * 
     * @param sql 转换后的 Oracle SQL
     * @return 添加存储配置后的 SQL
     */
    public static String postprocess(String sql) {
        if (sql == null || sql.trim().isEmpty()) {
            return sql;
        }
        
        String result = sql;
        
        // 1. 为 CREATE TABLE 语句添加存储配置（如果缺失）
        result = addTableStorageClause(result);
        
        // 2. 为 CREATE TABLE 中的主键约束添加存储配置（如果缺失）
        result = addPrimaryKeyStorageClause(result);
        
        // 3. 为 CREATE INDEX 语句添加存储配置（如果缺失）
        result = addIndexStorageClause(result);
        
        return result;
    }
    
    /**
     * 为 CREATE TABLE 语句添加存储配置（如果缺失）
     * 存储配置应该添加在表定义结束的最后一个 ) 后面
     */
    private static String addTableStorageClause(String sql) {
        // 匹配 CREATE TABLE 语句，找到列定义结束的最后一个 )
        // 使用括号计数来找到匹配的最后一个 )，而不是第一个 )
        StringBuffer result = new StringBuffer();
        Pattern createTablePattern = Pattern.compile(
            "(?i)CREATE\\s+TABLE",
            Pattern.CASE_INSENSITIVE
        );
        
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
                if (!inQuotes && (c == '"' || c == '\'')) {
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
                if (!inQuotes && (c == '"' || c == '\'')) {
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
                // 找到表定义结束位置
                String tableDef = sql.substring(startPos, tableDefEnd + 1);
                int semicolonPos = sql.indexOf(';', tableDefEnd + 1);
                if (semicolonPos > 0) {
                    String betweenParenAndSemicolon = sql.substring(tableDefEnd + 1, semicolonPos).trim();
                    
                    // 检查是否已有存储配置
                    boolean hasStorage = betweenParenAndSemicolon.toUpperCase().contains("SEGMENT CREATION") ||
                                       betweenParenAndSemicolon.toUpperCase().contains("PCTFREE") ||
                                       betweenParenAndSemicolon.toUpperCase().contains("TABLESPACE");
                    
                    if (!hasStorage) {
                        // 没有存储配置，添加默认配置
                        String storageClause = buildTableStorageClause();
                        result.append(tableDef).append(storageClause).append(";");
                    } else {
                        // 已有存储配置，保持不变
                        result.append(sql.substring(startPos, semicolonPos + 1));
                    }
                    lastIndex = semicolonPos + 1;
                } else {
                    // 没有找到分号，保持原样
                    result.append(sql.substring(startPos));
                    lastIndex = sql.length();
                }
            } else {
                // 没有找到匹配的 )，保持原样
                result.append(sql.substring(startPos));
                lastIndex = sql.length();
            }
        }
        
        result.append(sql.substring(lastIndex));
        return result.toString();
    }
    
    /**
     * 为 CREATE TABLE 中的主键约束添加存储配置（如果缺失）
     * 格式：CONSTRAINT "PK_NAME" PRIMARY KEY (columns) USING INDEX ... TABLESPACE ... ENABLE
     */
    private static String addPrimaryKeyStorageClause(String sql) {
        // 匹配 CREATE TABLE 中的主键约束
        // 模式：CONSTRAINT [约束名] PRIMARY KEY (列列表) [USING INDEX ...] [ENABLE]
        // 需要处理约束名可能有引号，列列表可能有多个列
        Pattern pkPattern = Pattern.compile(
            "(?i)(CONSTRAINT\\s+(?:[^\\s\"]+|\"[^\"]+\")\\s+PRIMARY\\s+KEY\\s*\\([^)]+\\))(\\s*(?:(?:USING\\s+INDEX|ENABLE)[^,);]*?)?)(?=\\s*[,)]|\\s*SEGMENT|\\s*PCTFREE|\\s*TABLESPACE|\\s*NOCOMPRESS|\\s*LOGGING|;|$)",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL
        );
        
        StringBuffer result = new StringBuffer();
        Matcher matcher = pkPattern.matcher(sql);
        
        while (matcher.find()) {
            String pkDef = matcher.group(1); // CONSTRAINT ... PRIMARY KEY (...)
            String afterPk = matcher.group(2); // PRIMARY KEY 后面的内容
            
            // 检查是否已有 USING INDEX 配置
            boolean hasUsingIndex = afterPk != null && 
                afterPk.trim().toUpperCase().contains("USING INDEX");
            
            if (!hasUsingIndex) {
                // 没有 USING INDEX 配置，添加默认配置
                String storageClause = buildPrimaryKeyStorageClause();
                matcher.appendReplacement(result, pkDef + storageClause);
            } else {
                // 已有配置，保持不变
                matcher.appendReplacement(result, matcher.group(0));
            }
        }
        matcher.appendTail(result);
        
        return result.toString();
    }
    
    /**
     * 为 CREATE INDEX 语句添加存储配置（如果缺失）
     */
    private static String addIndexStorageClause(String sql) {
        // 匹配 CREATE INDEX 语句，检查是否已有存储配置
        // 模式：CREATE [UNIQUE] INDEX ... ON ... (columns) ) [存储配置] ;
        // 使用更精确的匹配：匹配到 ) 和 ; 之间的内容
        Pattern indexPattern = Pattern.compile(
            "(?i)(CREATE\\s+(?:UNIQUE\\s+)?INDEX[\\s\\S]*?\\)\\s*)([^;]*?)(;)",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL
        );
        
        Matcher matcher = indexPattern.matcher(sql);
        StringBuffer sb = new StringBuffer();
        
        while (matcher.find()) {
            String indexDef = matcher.group(1); // CREATE INDEX ... )
            String betweenParenAndSemicolon = matcher.group(2); // ) 和 ; 之间的内容
            String semicolon = matcher.group(3); // 分号
            
            // 检查是否已有存储配置（检查是否包含 PCTFREE 或 TABLESPACE）
            boolean hasStorage = betweenParenAndSemicolon != null && 
                (betweenParenAndSemicolon.trim().toUpperCase().contains("PCTFREE") ||
                 betweenParenAndSemicolon.trim().toUpperCase().contains("TABLESPACE"));
            
            if (!hasStorage) {
                // 没有存储配置，添加默认配置
                String storageClause = buildIndexStorageClause();
                matcher.appendReplacement(sb, indexDef + storageClause + semicolon);
            } else {
                // 已有存储配置，保持不变
                matcher.appendReplacement(sb, matcher.group(0));
            }
        }
        matcher.appendTail(sb);
        
        return sb.toString();
    }
    
    /**
     * 构建表的存储配置子句
     */
    private static String buildTableStorageClause() {
        return "\n  SEGMENT CREATION IMMEDIATE \n" +
               "  PCTFREE 10 PCTUSED 40 INITRANS 1 MAXTRANS 255 \n" +
               "  NOCOMPRESS LOGGING\n" +
               "  STORAGE(INITIAL 65536 NEXT 1048576 MINEXTENTS 1 MAXEXTENTS 2147483645\n" +
               "  PCTINCREASE 0 FREELISTS 1 FREELIST GROUPS 1\n" +
               "  BUFFER_POOL DEFAULT FLASH_CACHE DEFAULT CELL_FLASH_CACHE DEFAULT)\n" +
               "  TABLESPACE \"" + DEFAULT_TABLESPACE + "\"";
    }
    
    /**
     * 构建主键约束的存储配置子句
     * 格式：USING INDEX PCTFREE 10 INITRANS 2 MAXTRANS 255 COMPUTE STATISTICS ... TABLESPACE ... ENABLE
     */
    private static String buildPrimaryKeyStorageClause() {
        return "\n  USING INDEX PCTFREE 10 INITRANS 2 MAXTRANS 255 COMPUTE STATISTICS \n" +
               "  STORAGE(INITIAL 65536 NEXT 1048576 MINEXTENTS 1 MAXEXTENTS 2147483645\n" +
               "  PCTINCREASE 0 FREELISTS 1 FREELIST GROUPS 1\n" +
               "  BUFFER_POOL DEFAULT FLASH_CACHE DEFAULT CELL_FLASH_CACHE DEFAULT)\n" +
               "  TABLESPACE \"" + DEFAULT_TABLESPACE + "\"  ENABLE";
    }
    
    /**
     * 构建索引的存储配置子句
     */
    private static String buildIndexStorageClause() {
        return "\n  PCTFREE 10 INITRANS 2 MAXTRANS 255 COMPUTE STATISTICS \n" +
               "  STORAGE(INITIAL 65536 NEXT 1048576 MINEXTENTS 1 MAXEXTENTS 2147483645\n" +
               "  PCTINCREASE 0 FREELISTS 1 FREELIST GROUPS 1\n" +
               "  BUFFER_POOL DEFAULT FLASH_CACHE DEFAULT CELL_FLASH_CACHE DEFAULT)\n" +
               "  TABLESPACE \"" + DEFAULT_TABLESPACE + "\"";
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
