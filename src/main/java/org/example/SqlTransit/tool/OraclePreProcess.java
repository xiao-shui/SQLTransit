package org.example.SqlTransit.tool;

import java.util.regex.Pattern;
import java.util.regex.Matcher;
import java.util.Set;
import java.util.LinkedHashSet;

/**
 * Oracle SQL 预处理类
 * 移除 JSqlParser 无法处理的 Oracle 特殊语法
 */
public class OraclePreProcess {
    
    /**
     * 预处理 Oracle SQL，移除特殊语法
     * 
     * @param sql 原始 Oracle SQL
     * @return 处理后的 SQL
     */
    public static String preprocess(String sql) {
        if (sql == null || sql.trim().isEmpty()) {
            return sql;
        }
        
        String result = sql;
        
        // 1. 先移除 USING INDEX ... ENABLE 整个子句（包括所有配置）
        // 必须在移除单独的 ENABLE 之前处理，避免误删
        result = removeUsingIndexClause(result);
        
        // 2. 移除约束后的 ENABLE 关键字（在约束定义末尾）
        result = removeConstraintEnable(result);
        
        // 3. 移除表定义后的存储配置（SEGMENT CREATION, PCTFREE, PCTUSED, INITRANS, MAXTRANS, NOCOMPRESS, LOGGING, STORAGE, TABLESPACE 等）
        result = removeTableStorageClause(result);
        
        // 4. 移除索引定义列括号内最后的逗号和数字参数（例如：("TENANT_ID_", 0) -> ("TENANT_ID_")）
        result = removeIndexColumnNumericParameter(result);
        
        // 5. 移除索引定义后的存储配置（PCTFREE, INITRANS, MAXTRANS, COMPUTE STATISTICS, STORAGE, TABLESPACE 等）
        result = removeIndexStorageClause(result);
        
        // 6. 替换 NUMBER(*,X) 中的 * 为 38（X 为任意数字）
        result = replaceNumberWildcard(result);
        
        // 7. 移除重复的 CREATE UNIQUE INDEX 语句（相同索引名和表名的重复索引）
        result = removeDuplicateUniqueIndexes(result);
        
        // 8. 清理多余的空格和换行
        result = cleanWhitespace(result);
        
        return result;
    }
    
    /**
     * 移除 USING INDEX ... ENABLE 整个子句
     * 包括 USING INDEX 及其后的所有配置直到 ENABLE
     */
    private static String removeUsingIndexClause(String sql) {
        // 匹配 USING INDEX 到 ENABLE 之间的所有内容（包括多行）
        // 需要匹配括号内的内容（STORAGE(...)等），使用非贪婪匹配
        Pattern pattern = Pattern.compile(
            "(?i)\\s+USING\\s+INDEX[\\s\\S]*?ENABLE\\s*",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL
        );
        return pattern.matcher(sql).replaceAll(" ");
    }
    
    /**
     * 移除约束后的 ENABLE 关键字
     * 例如：CONSTRAINT "PK_XXX" PRIMARY KEY (...) ENABLE
     * 或：CONSTRAINT "CKT_XXX" CHECK (...) ENABLE
     */
    private static String removeConstraintEnable(String sql) {
        // 匹配约束定义末尾的 ENABLE（在逗号、右括号或换行前）
        Pattern pattern = Pattern.compile(
            "(?i)\\s+ENABLE\\s*(?=[,\\)\\n])",
            Pattern.CASE_INSENSITIVE | Pattern.MULTILINE
        );
        return pattern.matcher(sql).replaceAll("");
    }
    
    /**
     * 移除表定义后的存储配置
     * 包括：SEGMENT CREATION IMMEDIATE, PCTFREE, PCTUSED, INITRANS, MAXTRANS, 
     * NOCOMPRESS, LOGGING, STORAGE(...), TABLESPACE 等
     */
    private static String removeTableStorageClause(String sql) {
        // 匹配表定义结束后的所有存储配置（从 ) 后到 ; 前）
        // 需要匹配多行，包括嵌套的括号（STORAGE(...)）
        // 使用非贪婪匹配，直到遇到分号
        Pattern pattern = Pattern.compile(
            "(?i)\\s*\\)\\s+(SEGMENT\\s+CREATION[\\s\\S]*?|PCTFREE[\\s\\S]*?|PCTUSED[\\s\\S]*?|INITRANS[\\s\\S]*?|MAXTRANS[\\s\\S]*?|NOCOMPRESS[\\s\\S]*?|LOGGING[\\s\\S]*?|STORAGE[\\s\\S]*?|TABLESPACE[\\s\\S]*?);",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL
        );
        Matcher matcher = pattern.matcher(sql);
        if (matcher.find()) {
            // 找到匹配，替换为 ) ;
            return matcher.replaceAll(" ) ;");
        }
        
        return sql;
    }
    
    /**
     * 移除索引定义列括号内最后的逗号和数字参数
     * 例如：("TENANT_ID_", 0) -> ("TENANT_ID_")
     *       ("COL1", "COL2", 0) -> ("COL1", "COL2")
     */
    private static String removeIndexColumnNumericParameter(String sql) {
        // 匹配 CREATE INDEX 语句中列定义括号内的数字参数
        // 模式：CREATE INDEX ... ON table (列名列表, 数字) 
        // 匹配括号内的最后一部分：逗号+数字，然后移除
        // 使用更灵活的模式，支持带引号的表名和schema前缀
        Pattern pattern = Pattern.compile(
            "(?i)(CREATE\\s+(?:UNIQUE\\s+)?INDEX\\s+[^\\s]+\\s+ON\\s+[^\\s(]+\\s*\\([^)]+?)(,\\s*\\d+\\s*)(\\))",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL
        );
        
        Matcher matcher = pattern.matcher(sql);
        StringBuffer sb = new StringBuffer();
        while (matcher.find()) {
            // 保留括号开始和列名部分，移除逗号和数字，保留右括号
            matcher.appendReplacement(sb, matcher.group(1) + matcher.group(3));
        }
        matcher.appendTail(sb);
        
        return sb.toString();
    }
    
    /**
     * 移除索引定义后的存储配置
     * 包括：PCTFREE, INITRANS, MAXTRANS, COMPUTE STATISTICS, STORAGE(...), TABLESPACE 等
     */
    private static String removeIndexStorageClause(String sql) {
        // 匹配索引定义后的存储配置（从 ) 后到 ; 前）
        // 模式：ON table (columns) 后的所有配置
        // 需要匹配多行，包括嵌套的括号
        Pattern pattern = Pattern.compile(
            "(?i)\\)\\s+(PCTFREE[\\s\\S]*?|INITRANS[\\s\\S]*?|MAXTRANS[\\s\\S]*?|COMPUTE\\s+STATISTICS[\\s\\S]*?|STORAGE[\\s\\S]*?|TABLESPACE[\\s\\S]*?);",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL
        );
        Matcher matcher = pattern.matcher(sql);
        if (matcher.find()) {
            // 替换为 ) ;
            return matcher.replaceAll(" ) ;");
        }
        
        return sql;
    }
    
    /**
     * 替换 NUMBER(*,X) 中的 * 为 38（X 为任意数字）
     */
    private static String replaceNumberWildcard(String sql) {
        // 匹配 NUMBER(*,X) 格式，支持空格，X 为任意数字
        Pattern pattern = Pattern.compile(
            "(?i)NUMBER\\s*\\(\\s*\\*\\s*,\\s*(\\d+)\\s*\\)",
            Pattern.CASE_INSENSITIVE
        );
        Matcher matcher = pattern.matcher(sql);
        StringBuffer sb = new StringBuffer();
        while (matcher.find()) {
            String scale = matcher.group(1); // 捕获后面的数字
            matcher.appendReplacement(sb, "NUMBER(38, " + scale + ")");
        }
        matcher.appendTail(sb);
        return sb.toString();
    }
    
    /**
     * 移除重复的 CREATE UNIQUE INDEX 语句
     * 对于相同索引名和表名的重复索引，只保留第一个，移除后续的重复项
     */
    private static String removeDuplicateUniqueIndexes(String sql) {
        // 匹配 CREATE UNIQUE INDEX 语句
        // 支持格式：CREATE UNIQUE INDEX "schema"."index_name" ON "schema"."table_name" (columns) ;
        // 或：CREATE UNIQUE INDEX "index_name" ON "table_name" (columns) ;
        Pattern indexPattern = Pattern.compile(
            "(?i)(CREATE\\s+UNIQUE\\s+INDEX\\s+[^\\s]+\\s+ON\\s+[^\\s(]+\\s*\\([^)]+\\)\\s*;)",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL
        );
        
        Matcher matcher = indexPattern.matcher(sql);
        Set<String> seenIndexes = new LinkedHashSet<>(); // 存储已见过的索引（索引名@表名）
        StringBuilder result = new StringBuilder();
        int lastEnd = 0;
        
        while (matcher.find()) {
            String indexStatement = matcher.group(1);
            
            // 提取索引名和表名
            // 匹配模式：CREATE UNIQUE INDEX "schema"."index_name" ON "schema"."table_name"
            // 或：CREATE UNIQUE INDEX "index_name" ON "table_name"
            Pattern extractPattern = Pattern.compile(
                "(?i)CREATE\\s+UNIQUE\\s+INDEX\\s+([^\\s]+)\\s+ON\\s+([^\\s(]+)",
                Pattern.CASE_INSENSITIVE
            );
            Matcher extractMatcher = extractPattern.matcher(indexStatement);
            
            if (extractMatcher.find()) {
                String indexFullName = extractMatcher.group(1).trim(); // 可能是 "schema"."index_name" 或 "index_name"
                String tableFullName = extractMatcher.group(2).trim(); // 可能是 "schema"."table_name" 或 "table_name"
                
                // 标准化索引名和表名（去除引号和schema前缀，统一为小写）
                String normalizedIndexName = normalizeIdentifier(indexFullName);
                String normalizedTableName = normalizeIdentifier(tableFullName);
                String indexKey = normalizedIndexName + "@" + normalizedTableName;
                
                // 如果这个索引已经出现过，跳过（移除重复）
                if (seenIndexes.contains(indexKey)) {
                    // 跳过这个重复的索引语句，不添加到结果中
                    // 但需要先追加前面未处理的内容，然后跳过当前匹配
                    result.append(sql.substring(lastEnd, matcher.start()));
                    lastEnd = matcher.end();
                } else {
                    // 首次出现，记录并保留
                    seenIndexes.add(indexKey);
                    result.append(sql.substring(lastEnd, matcher.end()));
                    lastEnd = matcher.end();
                }
            } else {
                // 如果无法提取索引名和表名，保留原语句
                result.append(sql.substring(lastEnd, matcher.end()));
                lastEnd = matcher.end();
            }
        }
        
        // 追加剩余部分
        result.append(sql.substring(lastEnd));
        
        return result.toString();
    }
    
    /**
     * 标准化标识符：去除引号、schema前缀，统一为小写
     * 例如："SC_JKZT"."PK_OBJ_TAB_REL" -> "pk_obj_tab_rel"
     *      "PK_OBJ_TAB_REL" -> "pk_obj_tab_rel"
     */
    private static String normalizeIdentifier(String identifier) {
        if (identifier == null) return "";
        // 去除所有引号
        String cleaned = identifier.replaceAll("[\"'`]", "");
        // 如果有schema前缀（包含点），取最后一部分
        if (cleaned.contains(".")) {
            cleaned = cleaned.substring(cleaned.lastIndexOf(".") + 1);
        }
        // 统一转为小写
        return cleaned.toLowerCase().trim();
    }
    
    /**
     * 清理多余的空格和换行
     */
    private static String cleanWhitespace(String sql) {
        // 将多个连续空格替换为单个空格
        sql = sql.replaceAll(" +", " ");
        // 将多个连续换行替换为单个换行
        sql = sql.replaceAll("\n{3,}", "\n\n");
        // 移除行尾空格
        sql = sql.replaceAll(" +\n", "\n");
        return sql.trim();
    }
    
    /**
     * 批量预处理多条 SQL 语句
     * 
     * @param sqls SQL 语句数组
     * @return 处理后的 SQL 语句数组
     */
    public static String[] preprocessBatch(String[] sqls) {
        if (sqls == null) {
            return null;
        }
        String[] results = new String[sqls.length];
        for (int i = 0; i < sqls.length; i++) {
            results[i] = preprocess(sqls[i]);
        }
        return results;
    }
}
