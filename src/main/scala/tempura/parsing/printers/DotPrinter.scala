package tempura.parsing.printers

import tempura.expression.Core.{InterpEnv, TypeEnv}
import tempura.helpers.Utils.OS.{Linux, Mac, Unknown}
import tempura.helpers.Utils.unexpected
import tempura.helpers.Utils
import tempura.transitions.LabeledGraph

import java.io.{File, PrintWriter}
import java.nio.file.{Files, Path, Paths}
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

  object StateGraphPrinter
  
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
            s"${x.toString} [shape=${nodeConfig(x).nodeShape}, color=${nodeConfig(x).nodeColor} ${nodePrinter.map(l => "label=\"" + l(x) + "\"").getOrElse("")} ${nodeConfig(x).nodeStyle.map(s => s", style=$s").getOrElse("")}]")
          .mkString("\n") +
        "\n" + /* Individual edges list */
        edges.map(e => s"${e._1.toString} -> ${e._3.toString} [color=${edgeConfig(e).edgeColor}, style=${edgeConfig(e).edgeStyle} ${edgePrinter.map(l => ", label=\"" + l(e) + "\"").getOrElse("") + " "}]")
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

    /**
     * Opens the PDF using the first available PDF viewer.
     * On Linux, checks for installed viewers in preference order.
     * On macOS, uses the system `open` command.
     */
    private def openPdf(path: Path): Unit = {
      Utils.getOS match {
        case Mac =>
          Seq("open", path.toString).!

        case Linux =>
          // Check for installed PDF viewers in preference order
          findFirstAvailableViewer() match {
            case Some(viewer) =>
              Seq(viewer, path.toString).!
            case None =>
              // Ultimate fallback: xdg-open (should always work on Linux)
              println(s"[warn] No known PDF viewer found, using xdg-open.")
              Seq("xdg-open", path.toString).!
          }

        case Unknown(os) =>
          println(s"[warn] Unsupported OS '${os}'; cannot open PDF automatically: $path")
      }
    }

    /**
     * Find the first available PDF viewer from a list of known viewers.
     * Checks in preference order: okular, evince, atril, qpdfview, mupdf, xpdf.
     * Uses `which` to test if each viewer is installed and executable.
     */
    private def findFirstAvailableViewer(): Option[String] = {
      val pdfViewers = List(
        "okular",      // KDE default
        "evince",      // GNOME default
        "atril",       // MATE default
        "qpdfview",    // Lightweight Qt viewer
        "mupdf",       // Minimal viewer
        "xpdf"         // Classic X11 viewer
      )

      pdfViewers.find { viewer =>
        try {
          // Check if viewer is in PATH using `which`
          val exitCode = Seq("which", viewer).!
          exitCode == 0
        } catch {
          case _: Exception => false
        }
      }
    }
  }
}