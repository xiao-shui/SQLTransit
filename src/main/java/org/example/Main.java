package org.example;

import net.sf.jsqlparser.JSQLParserException;
import net.sf.jsqlparser.parser.CCJSqlParserUtil;
import net.sf.jsqlparser.statement.Statement;
import org.example.SqlTransitAI.tool.MysqlToOracleVisitor;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Scanner;

/**
 * 针对DDL和DML脚本的SQL分析工具
 */
public class Main {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        System.out.print("请输入SQL脚本文件路径: ");
        String filePath = scanner.nextLine();

        String mysqlSql;
        try {
            mysqlSql = Files.readString(Paths.get(filePath));
        } catch (Exception e) {
            System.err.println("读取文件失败: " + e.getMessage());
            return;
        }

        List<Statement> statements = null;
        try {
            statements = CCJSqlParserUtil.parseStatements(mysqlSql).getStatements();
        } catch (JSQLParserException e) {
            System.err.println("解析SQL失败: " + e.getMessage());
            return;
        }

        MysqlToOracleVisitor visitor = new MysqlToOracleVisitor();
        for (Statement stmt : statements) {
            stmt.accept(visitor);
        }
        System.out.println(visitor.getOracleSql());
    }
}
