# Copyright (c) 2012-2014, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import os, glob, string

env = DefaultEnvironment(ENV = os.environ, tools=['default', 'Coq'])

# Coq dependencies
vs = glob.glob('*.v')
if os.system('coqdep ' + ' '.join(map(str, vs)) + ' -R . "" > deps'): Exit(2)
ParseDepends('deps')

# coq2html
env.Command('./utils/coq2html.ml', 'utils/coq2html.mll',
  'ocamllex -q $SOURCE -o $TARGET')
t = env.Command('utils/coq2html', 'utils/coq2html.ml',
  'ocamlopt -o $TARGET str.cmxa $SOURCE')
env.Clean(t, 'utils/coq2html.o')
env.Clean(t, 'utils/coq2html.cmi')
env.Clean(t, 'utils/coq2html.cmx')

# Coq files
for v in vs:
  env.Coq(v, COQFLAGS='-R . ""')
  h = 'doc/' + os.path.splitext(v)[0] + '.html'
  glo = os.path.splitext(v)[0] + '.glob'
  env.Command(h, ['utils/coq2html', v, glo],
    'utils/coq2html -o '+h+' '+glo+' '+v)

# Parser
main = env.Command(['ch2o','ch2o.byte'], '', 'ocamlbuild -j 2 -libs nums\
  -pp \'grep -v "^#"\' -I parser parser/Main.native parser/Main.byte &&\
  mv Main.native ch2o && mv Main.byte ch2o.byte')
AlwaysBuild(main)
env.Clean('extraction.vo', 'parser/Extracted.ml')
env.Clean('extraction.vo', 'parser/Extracted.mli')
env.Depends(main, 'extraction.vo')
env.Clean(main, '_build')

# Coqidescript
env.CoqIdeScript('coqidescript', [], COQFLAGS='-R . ""')
