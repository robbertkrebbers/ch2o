# Copyright (c) 2012-2014, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import os, glob, string

env = DefaultEnvironment(
	ENV = os.environ, tools=['default', 'Coq', 'Ocaml']
)

# Coq dependencies
vs = glob.glob('*.v')
if os.system('coqdep ' + ' '.join(map(str, vs)) + ' -R . "" > deps'): Exit(2)
ParseDepends('deps')

# coq2html
env.OcamlLex('utils/coq2html')
env.OcamlProg('utils/coq2html', OCAMLFLAGS='str.cma')

# Coq files
for v in vs:
  env.Coq(v, COQFLAGS='-R . ""')
  h = 'doc/' + os.path.splitext(v)[0] + '.html'
  glo = os.path.splitext(v)[0] + '.glob'
  env.Command(h, ['utils/coq2html', v, glo],
    'utils/coq2html -o '+h+' '+glo+' '+v)

# Parser
main = env.Command('Main.native', '', 'ocamlbuild -j 2 -libs nums\
  -I parser parser/Main.native && mv Main.native ch2o')
env.Depends(main, 'extraction.vo')

# Coqidescript
env.CoqIdeScript('coqidescript', [], COQFLAGS='-R . ""')
