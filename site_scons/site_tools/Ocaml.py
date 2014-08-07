# Copyright (c) 2012-2014, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import SCons.Defaults, SCons.Tool, SCons.Util, os

def ocamlprog_emitter(target, source, env):
  base, _ = os.path.splitext(str(target[0]))
  target.append(base + ".cmi")
  return target, source
def ocamlyacc_emitter(target, source, env):
  base, _ = os.path.splitext(str(target[0]))
  target.append(base + ".mli")
  return target, source

OCAML = SCons.Builder.Builder(
  action = '$OCAMLC $OCAMLFLAGS -c $SOURCE',
  suffix = '.cmo',
  src_suffix = '.ml'
)
OCAMLPROG = SCons.Builder.Builder(
  action = '$OCAMLC $OCAMLFLAGS -o $TARGET $SOURCE',
  src_suffix = '.ml',
  suffix = '',
  emitter = ocamlprog_emitter
)
OCAMLI = SCons.Builder.Builder(
  action = '$OCAMLC $OCAMLFLAGS -c $SOURCE',
  suffix = '.cmi',
  src_suffix = '.mli',
)
OCAMLLEX = SCons.Builder.Builder(
  action = '$OCAMLLEX $SOURCE',
  suffix = '.ml',
  src_suffix = '.mll',
)
OCAMLYACC = SCons.Builder.Builder(
  action = '$OCAMLYACC $SOURCE',
  suffix = '.ml',
  src_suffix = '.mly',
  emitter = ocamlyacc_emitter
)

def generate(env):
  env['OCAMLC'] = 'ocamlc'
  env['OCAMLLEX'] = 'ocamllex'
  env['OCAMLYACC'] = 'ocamlyacc'
  env.Append(BUILDERS = {
    'Ocaml' : OCAML, 'OcamlI' : OCAMLI, 'OcamlProg' : OCAMLPROG,
    'OcamlLex' : OCAMLLEX, 'OcamlYacc' : OCAMLYACC
  })

def exists(env):
  return env.Detect('ocaml')
