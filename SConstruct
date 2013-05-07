# Copyright (c) 2012-2013, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.

import os, glob, string

env = DefaultEnvironment(ENV = os.environ, tools=['default', 'Coq'])
vs = glob.glob('./*.v')
Rs = '-R . ""'

if os.system('coqdep ' + ' '.join(map(str, vs)) + ' ' + Rs + ' > deps'):
	Exit(2)

ParseDepends('deps')

for v in vs:
  env.Coq(v, COQFLAGS=Rs)
  h = 'doc/' + os.path.splitext(v)[0] + '.html'
  vo = os.path.splitext(v)[0] + '.vo'
  g = os.path.splitext(v)[0] + '.glob'
  env.Command(h, ['utils/coq2html', v, g],
    'utils/coq2html -o ' + h + ' ' + g + ' ' + v)

env.Command('./utils/coq2html.ml', 'utils/coq2html.mll',
  'ocamllex -q $SOURCE -o $TARGET')
t = env.Command('utils/coq2html', 'utils/coq2html.ml',
  'ocamlopt -o $TARGET str.cmxa $SOURCE')
Clean(t, 'utils/coq2html.o')
Clean(t, 'utils/coq2html.cmi')
Clean(t, 'utils/coq2html.cmx')

env.CoqIdeScript('coqidescript', [], COQFLAGS=Rs)

