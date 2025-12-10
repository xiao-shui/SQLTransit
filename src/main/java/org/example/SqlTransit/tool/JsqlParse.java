package org.example.SqlTransit.tool;

import net.sf.jsqlparser.parser.CCJSqlParserUtil;
import net.sf.jsqlparser.statement.Statement;
import net.sf.jsqlparser.statement.Statements;

import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.HashSet;
import java.util.Scanner;
import java.util.Set;

public class JsqlParse {

    public static void main(String[] args) throws Exception {
        Scanner scanner = new Scanner(System.in);
        System.out.print("请输入SQL脚本文件路径: ");
        String filePath = scanner.nextLine();

        String sql;
        try {
            sql = Files.readString(Paths.get(filePath));
        } catch (Exception e) {
            System.err.println("读取文件失败: " + e.getMessage());
            return;
        }

        Statements statements;
        try {
            statements = CCJSqlParserUtil.parseStatements(sql);
        } catch (Exception e) {
            System.err.println("SQL解析失败: " + e.getMessage());
            return;
        }
        for (Statement stmt : statements.getStatements()) {
            printAst(stmt, 0, new HashSet<>());
            System.out.println();
        }
    }
    // 递归打印对象树
    static void printAst(Object node, int indent, Set<Object> seen) {
        if (node == null) return;
        // 防止循环引用（部分节点有父节点引用）
        if (seen.contains(node)) return;
        seen.add(node);
        // 打印当前节点信息
        printIndent(indent);
        System.out.print(node.getClass().getSimpleName());
        String value = node.toString();
        // 截断内容，避免太冗长
        value = value.length() > 80 ? value.substring(0,78)+"..." : value;
        System.out.println(": " + value);
        // 递归调用。遍历所有getter方法
        Method[] methods = node.getClass().getMethods();
        for (Method m : methods) {
            if (m.getName().startsWith("get") && m.getParameterCount() == 0
                    && !m.getName().equals("getClass")) {
                try {
                    Object child = m.invoke(node);
                    if (child == null) continue;
                    // 集合类型，需要递归
                    if (child instanceof Collection<?> coll) {
                        if (coll.isEmpty()) continue;
                        printIndent(indent+1);
                        System.out.println("-- " + m.getName() + " --");
                        for (Object c : coll) {
                            printAst(c, indent+2, seen);
                        }
                    } else if (!isJavaType(child)) {
                        printIndent(indent+1);
                        System.out.println("-- " + m.getName() + " --");
                        printAst(child, indent+2, seen);
                    }
                } catch (Exception ignore) {}
            }
        }
    }
    // 简化排除常见基础类型
    static boolean isJavaType(Object obj) {
        Class<?> c = obj.getClass();
        return c.getName().startsWith("java.") ||
                c.isPrimitive() ||
                c == String.class ||
                c == Integer.class ||
                c == Long.class ||
                c == Short.class ||
                c == Boolean.class ||
                c == Double.class ||
                c == Float.class ||
                c == Character.class ||
                c == Byte.class;
    }
    static void printIndent(int indent) {
        for (int i=0; i<indent; i++) System.out.print("  ");
    }
}
