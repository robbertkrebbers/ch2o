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
def depends_parser():
  if os.system('ocamldep -I parser parser/*.ml\
    parser/*.mli > parser/deps'): Exit(2)
  ParseDepends('parser/deps')
depends_parser();

parser = env.OcamlYacc('parser/Parser')
lexer = env.OcamlLex('parser/Lexer')
env.Depends(lexer, parser)
env.Depends('parser/Lexer.mli', lexer)

def parser_hook(target, source, env): depends_parser()
AddPostAction([lexer,parser], parser_hook)

mlis = ['parser/Cerrors.mli', 'parser/Parse_aux.mli',
  'parser/Parser.mli', 'parser/Lexer.mli']
for mli in mlis: env.OcamlI(mli, OCAMLFLAGS='-I parser')
mls = ['parser/Cerrors.ml', 'parser/Cabs.ml', 'parser/Cabshelper.ml',
	'parser/Parse_aux.ml', 'parser/Parser.ml', 'parser/Lexer.ml']
for ml in mls: env.Ocaml(ml, OCAMLFLAGS='-I parser')

# Coqidescript
env.CoqIdeScript('coqidescript', [], COQFLAGS='-R . ""')

# Extraction
def depends_extraction():
  if os.system('ocamldep -I extraction extraction/*.ml\
    extraction/*.mli > ./extraction/deps'): Exit(2)
  ParseDepends('extraction/deps')
depends_extraction()

def extraction_hook(target, source, env):
  depends_extraction()
  mls = glob.glob('extraction/*.ml')
  for ml in mls:
    mli = os.path.splitext(ml)[0]
    env.OcamlI(mli, OCAMLFLAGS='-I extraction')
    t = env.Ocaml(ml, OCAMLFLAGS='-I extraction')
    env.Depends('extraction', t)
AddPostAction('extraction.vo', extraction_hook)
env.Clean('extraction.vo', glob.glob('extraction/*.ml'))
env.Clean('extraction.vo', glob.glob('extraction/*.mli'))
env.Clean('extraction.vo', glob.glob('extraction/*.cmo'))
env.Clean('extraction.vo', glob.glob('extraction/*.cmi'))

