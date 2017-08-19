# Emacs this is -*- perl -*-
#
# Based on https://tex.stackexchange.com/a/37730/1340.
# Assuming your main document file is called foo:
# - The static preamble should be in foo.ltx
# - Precompiled preamble will be in foo.fmt.
# - The first time the preamble must be compiled by hand.
# - Main document without preamble should be in foo.tex.
#   Its first line should start with '%&foo' (without quotes).

# If you use another processor rather than pdflatex, replace both
# occurrences of pdflatex below (especially the second) with your TeX
# processor (etex, latex, lualatex, etc.)

# Enable correct dependency tracking.
$pdflatex="pdflatex -synctex=1 -file-line-error -interaction=nonstopmode -halt-on-error %O %S";
$recorder = 1;
# Declare that pdflatex also reads .fmt files.
add_input_ext('pdflatex','fmt');
# fmt files are built from ltx files by calling the compilepreamble function defined below.
add_cus_dep('ltx', 'fmt', 0, 'compilepreamble');
sub compilepreamble {
    print "Preamble compiling for '$_[0]'...\n";
    my $fls_file = "$_[0].fls";
    my $source = "$_[0].ltx";
    my $fmt_file = "$_[0].fmt";
    # Precompile format file.
    my $return = system( "pdflatex",
                         "-ini", "-recorder", "-jobname=$_[0]",
                         "&pdflatex $source \\dump" );
    if ($return) {
       warn "Error in making format file '$fmt_file'\n";
       return $return;
    }
    my %input_files = ();
    my %output_files = ();
    $return = parse_fls( $fls_file, \%input_files, \%output_files );
    if ($return) {
        warn "No fls file '$fls_file' made; I cannot get dependency data\n";
        return 0;
    }
    # Use latexmk's internal variables and subroutines for setting the
    #   dependency information.
    # Note that when this subroutine is called to implement a custom
    #   dependency, the following variables are set:
    #       $rule  contains the name of the current rule (as in the
    #              fdb_latexmk file)
    #       $PHsource is a pointer to a hash of source file
    #              information for the rule.  The keys of the hash are
    #              the names of the source files of the rule.
    foreach my $file (keys %input_files) {
        rdb_ensure_file( $rule, $file );
    }
    foreach my $file (keys %$PHsource) {
        if ( ! exists $input_files{$file} ) {
            print "   Source file of previous run '$file' ",
                  "IS NO LONGER IN USE\n";
            rdb_remove_files( $rule, $file );
        }
    }
    return 0;
};
