import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.*;
import java.nio.file.*;
import java.nio.charset.StandardCharsets;

public class RunAll {
  public static void main(String[] args) throws Exception {
    CompModule m = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, args[0]);
    A4Options o = new A4Options();
    System.out.println("A4Options default noOverflow=" + o.noOverflow);
    o.noOverflow = Boolean.parseBoolean(args[2]);
    System.out.println("Effective noOverflow=" + o.noOverflow);
    o.solver = A4Options.SatSolver.SAT4J;
    Path out = Paths.get(args[1]);
    Files.createDirectories(out);
    StringBuilder log = new StringBuilder("index\tlabel\tkind\tresult\telapsed_ms\tcommand\n");
    int i = 0;
    for (Command c : m.getAllCommands()) {
      long start = System.nanoTime();
      A4Solution s = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, m.getAllReachableSigs(), c, o);
      long ms = (System.nanoTime() - start) / 1000000;
      String row = i + "\t" + c.label + "\t" + (c.check ? "check" : "run") + "\t" +
        (s.satisfiable() ? "SAT" : "UNSAT") + "\t" + ms + "\t" + c + "\n";
      log.append(row);
      System.out.print(row);
      if (s.satisfiable()) s.writeXML(out.resolve(i + "_" + c.label + ".xml").toString());
      i++;
    }
    Files.write(out.resolve("results.tsv"), log.toString().getBytes(StandardCharsets.UTF_8));
  }
}
