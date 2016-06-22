Paolo, Tillmann and Cai decided on 18.06.2013 the following
guidelines about collaborating on [the paper][1].

1. Each newly-written line should be no more than 65 characters
long. Adding the following code to `$HOME/.emacs` should enforce
it automatically:

        (defun activate-auto-fill-in-TeX-mode () (auto-fill-mode 1))
        (add-hook 'LaTeX-mode-hook 'activate-auto-fill-in-TeX-mode)

To set the fill-column globally to 65, you can also add:

        (setq-default fill-column 65)

However, the content of .dir-locals.el should enforce that for
latex files in the current directory.

To ensure that a particular file is recognized as LaTeX, even
when Emacs doesn't figure that out automatically, you just need
the following annotation to the top line to ensure that other
files are recognized as LaTeX files and not as TeX ones (where
the settings don't apply):

		% Emacs, this is -*- latex -*-!

2. Edits should be made with the appearance of the diff page on
GitHub in mind. The command `git add -p <files>` should help, as
should `git diff --color-words <file>`.

3. Use macros for a uniform appearance and flexibility to settle
on notational details later.

        \App{f}{x}    for  f x
        \Lam{x}{t}    for  λx. t
        \apply{dv}{v} for  "apply the change dv to the value v"
        \diff{u}{v}   for  "the change from v toward u"

4. Put each section and figure
lazily in a separate file. "Introduction",
for instance, may be moved to `POPL14/paper/sec-intro.tex` the
next time someone writes in it.

[1]: https://github.com/ps-mr/ilc/blob/master/POPL14/paper/pldi14-ilc.tex

