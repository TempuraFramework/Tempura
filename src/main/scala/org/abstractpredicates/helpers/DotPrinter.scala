package org.abstractpredicates.helpers

import org.abstractpredicates.helpers.Utils.OS.{Linux, Mac, Unknown}
import org.abstractpredicates.helpers.Utils.unexpected
import org.abstractpredicates.transitions.LabeledGraph

import java.nio.file.{Files, Paths, Path}
import java.io.{File, PrintWriter}
import scala.sys.process.*


object DotPrinter {

  enum NodeShapes {
    case Box, Plaintext, Triangle, InvTriangle

    override def toString: String = {
      this match {
        case Box => "box"
        case Plaintext => "plaintext"
        case Triangle => "triangle"
        case InvTriangle => "invtriangle"
      }
    }
  }

  enum EdgeStyles {
    case Solid, Dashed, Dotted, Bold, Invis

    override def toString: String = {
      this match {
        case Solid => "solid"
        case Dashed => "dashed"
        case Dotted => "dotted"
        case Bold => "bold"
        case Invis => "invis"
      }
    }
  }

  case class NodeConfig(nodeShape: NodeShapes, nodeColor: String, nodeStyle: Option[String])

  case class EdgeConfig(edgeColor: String, edgeStyle: EdgeStyles)

  final val defaultNodeConfig = NodeConfig(NodeShapes.Box, "black", None)
  final val defaultEdgeConfig = EdgeConfig("black", EdgeStyles.Solid)

  case class Printer[NodeLabel, EdgeLabel](graph: LabeledGraph[NodeLabel, EdgeLabel],
                                           isDirected: Boolean,
                                           nodeConfig: graph.Vertex => NodeConfig,
                                           edgeConfig: graph.Edge => EdgeConfig,
                                           nodePrinter: Option[graph.Vertex => String] = None,
                                           edgePrinter: Option[graph.Edge => String] = None) {

    private final val dotPreamble =
      (if isDirected then "strict digraph {\n" else "strict graph {\n")

    private final val dotPostamble = "\n}\n"

    def dotString: String = {
      val nodes = graph.allNodes
      val edges = graph.allEdges
      val dot = dotPreamble +
        nodes.map(x => /* Individual nodes list */
            s"${x.toString} [shape=${nodeConfig(x).nodeShape}, color=${nodeConfig(x).nodeColor} ${nodePrinter.map(l => "label=\"" + l(x)).getOrElse("") + "\""} ${nodeConfig(x).nodeStyle.map(s => s", style=$s").getOrElse("")}]")
          .mkString("\n") +
        "\n" + /* Individual edges list */
        edges.map(e => s"${e._1.toString} -> ${e._3.toString} [color=${edgeConfig(e).edgeColor}, style=${edgeConfig(e).edgeStyle} ${edgePrinter.map(l => "label=\"" + l(e)).getOrElse("") + "\""}]")
          .mkString("\n") +
        dotPostamble
      dot
    }

    /**
     * Render DOT to PDF, optionally open it.
     *
     * @param outputPdf Optional output path. If None, a temporary file is created.
     * @param open      Whether to open the PDF after generating it.
     * @return The final PDF path.
     */
    def visualizeDOT(outputPdf: Option[Path] = None, open: Boolean = true): Path = {
      val dot = this.dotString

      // 1. Produce a temporary DOT file
      val dotFile = Files.createTempFile("graph_", ".dot")
      val writer = new PrintWriter(dotFile.toFile)
      try writer.write(dot)
      finally writer.close()

      // 2. Determine PDF output path
      val pdfFile = outputPdf.getOrElse {
        Files.createTempFile("graphviz_", ".pdf")
      }

      // 3. Call Graphviz
      val dotCmd = Seq("dot", "-Tpdf", dotFile.toString, "-o", pdfFile.toString)
      val exit = dotCmd.!

      if exit != 0 then
        throw new RuntimeException(s"Graphviz failed with exit code $exit")

      // 4. Optionally open the PDF
      if open then openPdf(pdfFile)

      pdfFile
    }

    /** Opens the PDF based on OS + Environment. */
    private def openPdf(path: Path): Unit = {
      Utils.getOS match {
        case Mac =>
          Seq("open", path.toString).!

        case Linux =>
          Utils.getLinuxDesktop match {
            case Some("kde") =>
              // Okular is default for KDE
              Seq("okular", path.toString).!

            case Some("gnome") =>
              // GNOME default viewer is `evince`
              Seq("evince", path.toString).!
            case _ =>
              // fallback if unknown Linux desktop
              println(s"[warn] Unknown desktop environment, falling back to xdg-open.")
              Seq("xdg-open", path.toString).!
          }
        case Unknown(os) =>
          println(s"[warn] Unsupported OS ${os}; cannot open PDF automatically: $path")
      }
    }

  }
}