all: startup scalagraph jdkgraph

startup:
	Rscript plotdata2.r
scalagraph:
	Rscript plotdata.r LOSTestLog-ScalaTest.csv
scalared: scalagraph
	pdflatex EvalRed
	pdflatex EvalRed
	mv EvalRed.pdf EvalRed-scalatest.pdf
jdkgraph:
	Rscript plotdata.r LOSTestLog-JDK.csv --restOnly
	Rscript plotdata.r LOSTestLog-JDK-idxes-update.csv --idxOnly
jdkred: jdkgraph
	pdflatex EvalRed
	pdflatex EvalRed
	mv EvalRed.pdf EvalRed-jdk.pdf
forposter:
	xelatex EvalTableHarness
	xelatex EvalSummaryTableHarness
