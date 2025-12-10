package org.example;

import net.sf.jsqlparser.JSQLParserException;
import net.sf.jsqlparser.parser.CCJSqlParserUtil;
import net.sf.jsqlparser.statement.Statement;
import org.example.SqlTransit.tool.MysqlToOracleVisitor;
import org.example.SqlTransit.tool.MysqlToPostgresqlVisitor;
import org.example.SqlTransit.tool.OracleToMysqlVisitor;
import org.example.SqlTransit.tool.PostgresqlToMysqlVisitor;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Scanner;

/**
 * 针对DDL和DML脚本的SQL分析工具
 */
public class Main {
    public static void main(String[] args) {
        MysqlToOracleVisitor mysqlToOracleVisitor = new MysqlToOracleVisitor();
        MysqlToPostgresqlVisitor mysqlToPostgresqlVisitor = new MysqlToPostgresqlVisitor();
        OracleToMysqlVisitor oracleToMysqlVisitor = new OracleToMysqlVisitor();
        PostgresqlToMysqlVisitor postgresqlToMysqlVisitor=new PostgresqlToMysqlVisitor();
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
            System.out.print("请输入来源方言: ");
            String FromName = scanner.nextLine();
            System.out.print("请输入目标方言: ");
            String ToName = scanner.nextLine();
            if(FromName.toLowerCase().equals("mysql")&&ToName.toLowerCase().equals("oracle")){
                for (Statement stmt : statements) {
                    stmt.accept(mysqlToOracleVisitor);
                }
                System.out.println(mysqlToOracleVisitor.getOracleSql());
            }else if(FromName.toLowerCase().equals("mysql")&&ToName.toLowerCase().equals("postgresql")){
                for (Statement stmt : statements) {
                    stmt.accept(mysqlToPostgresqlVisitor);
                }
                System.out.println(mysqlToPostgresqlVisitor.getPostgresqlSql());
            }else if(FromName.toLowerCase().equals("oracle")&&ToName.toLowerCase().equals("mysql")){
                for (Statement stmt : statements) {
                    stmt.accept(oracleToMysqlVisitor);
                }
                System.out.println(oracleToMysqlVisitor.getMysqlSql());
            }else if(FromName.toLowerCase().equals("postgresql")&&ToName.toLowerCase().equals("mysql")){
                for (Statement stmt : statements) {
                    stmt.accept(postgresqlToMysqlVisitor);
                }
                System.out.println(postgresqlToMysqlVisitor.getMysqlSql());
            }
        }

}
