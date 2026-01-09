package org.example.SqlTransit.tool;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

/**
 * PostgreSQL SQL 预处理类
 * 移除 JSqlParser 无法处理的 PostgreSQL 特殊语法
 */
public class PGPreProcess {
    
    /**
     * 预处理 PostgreSQL SQL，移除特殊语法
     * 
     * @param sql 原始 PostgreSQL SQL
     * @return 处理后的 SQL
     */
    public static String preprocess(String sql) {
        if (sql == null || sql.trim().isEmpty()) {
            return sql;
        }
        
        String result = sql;
        
        // 1. 移除 :: 类型转换语法（例如：::character varying NULL, ::text, ::integer 等）
        result = removeTypeCast(result);
        
        // 2. 清理多余的空格和换行
        result = cleanWhitespace(result);
        
        return result;
    }
    
    /**
     * 移除 PostgreSQL 的类型转换语法 ::type
     * 例如：
     * - column_name::character varying NULL -> column_name NULL
     * - column_name::text -> column_name
     * - column_name::integer -> column_name
     * - column_name::character varying -> column_name
     * - column_name::varchar(255) -> column_name
     */
    private static String removeTypeCast(String sql) {
        // 匹配 :: 后面跟类型名（可能包含空格、括号和参数），直到遇到关键字、逗号、分号、右括号等分隔符
        // 支持的类型名：character varying, varchar, text, integer, bigint, numeric, timestamp, date 等
        // 模式：:: 后面跟类型名（可能包含括号和参数），直到遇到关键字（如 NULL, NOT, DEFAULT 等）或分隔符
        // 使用非贪婪匹配，遇到关键字或分隔符时停止
        // 匹配 ::type 格式，type 可以是单个词或带空格的词组（如 character varying）
        Pattern pattern = Pattern.compile(
            "::\\s*[a-zA-Z_][a-zA-Z0-9_\\s()]*(?=\\s*(?:NULL|NOT|DEFAULT|PRIMARY|UNIQUE|CHECK|,|;|\\)|$))",
            Pattern.CASE_INSENSITIVE
        );
        
        Matcher matcher = pattern.matcher(sql);
        StringBuffer sb = new StringBuffer();
        while (matcher.find()) {
            // 移除整个匹配（包括 :: 和类型名）
            matcher.appendReplacement(sb, "");
        }
        matcher.appendTail(sb);
        
        return sb.toString();
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
