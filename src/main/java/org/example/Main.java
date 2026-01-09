package org.example;

import net.sf.jsqlparser.JSQLParserException;
import net.sf.jsqlparser.parser.CCJSqlParserUtil;
import net.sf.jsqlparser.statement.Statement;
import org.example.SqlTransit.tool.*;
import org.example.SqlTransit.tool.OraclePreProcess;


import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.nio.charset.StandardCharsets;
import java.util.List;

/**
 * 针对DDL和DML脚本的SQL分析工具
 */
public class Main {
    public static void main(String[] args) {
//        OracleToGDBVisitor oracleToGDBVisitor = new OracleToGDBVisitor();
//        MysqlToOracleVisitor mysqlToOracleVisitor = new MysqlToOracleVisitor();
//        OracleToMysqlVisitor oracleToMysqlVisitor = new OracleToMysqlVisitor();
//        MysqlToPGVisitor mysqlToPGVisitor = new MysqlToPGVisitor();
        PGToMysqlVisitor pgToMysqlVisitor = new PGToMysqlVisitor();
//        OracleToPGVisitor oracleToPGVisitor = new OracleToPGVisitor();
        PGToOracleVisitor pgToOracleVisitor = new PGToOracleVisitor();


        String filePath = "D:\\桌面\\脚本\\PG脚本.sql";
        String outputPath = "D:\\桌面\\脚本\\result.sql";
        String mysqlSql = null;
        List<Statement> statements = null;
        try {
            mysqlSql = Files.readString(Paths.get(filePath));
        } catch (Exception e) {
            System.err.println("读取文件失败: " + e.getMessage());
        }

        //mysqlSql=PGPreProcess.preprocess(mysqlSql);
        mysqlSql = OraclePreProcess.preprocess(mysqlSql);

        try {
            statements = CCJSqlParserUtil.parseStatements(mysqlSql).getStatements();
        } catch (JSQLParserException e) {
            System.err.println("解析SQL失败: " + e.getMessage());
        }

        for (Statement stmt : statements) {
            stmt.accept(pgToMysqlVisitor);
        }

        String resultSql = pgToMysqlVisitor.getMysqlSql();

        //resultSql = GDBPosProcess.postprocess(resultSql);

        try {
            Files.writeString(
                    Paths.get(outputPath),
                    resultSql,
                    StandardCharsets.UTF_8,
                    StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING
            );
            System.out.println("转换结果已写入: " + outputPath);
        } catch (Exception e) {
            System.err.println("写入结果文件失败: " + e.getMessage());
        }
    }
}
