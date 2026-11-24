# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
## Small CLI over the Nim bindings: crux_cli <command> FILE
##   commands: lex parse lower emit-smt emit-lean emit-sas emit-cuda cert check run solve
##   crux_cli abjad WORD...

import std/[os, strutils]
import crux

proc usage() =
  stderr.writeLine "usage: crux_cli <lex|parse|lower|emit-smt|emit-lean|emit-sas|emit-cuda|cert|check|run|solve> FILE"
  stderr.writeLine "       crux_cli abjad WORD..."
  stderr.writeLine "       crux_cli version"
  quit 2

proc main() =
  let args = commandLineParams()
  if args.len == 0: usage()
  let cmd = args[0]
  if cmd == "version":
    echo "libcrux ", version()
    return
  if cmd == "abjad":
    for w in args[1 .. ^1]:
      let v = abjadValue(w)
      echo w, "\t", v, "\tdigit_root=", digitRoot(v)
    return
  if args.len != 2: usage()
  let src = readFile(args[1])
  let f = case cmd
    of "lex": lex
    of "parse": parse
    of "lower": lower
    of "emit-smt": emitSmt
    of "emit-lean": emitLean
    of "emit-sas": emitSas
    of "emit-cuda": emitCuda
    of "cert": cert
    of "check": check
    of "run": run
    of "solve": solve
    else:
      usage()
      lex
  try:
    stdout.write f(src)
  except CruxError as e:
    stderr.writeLine e.msg.replace("<input>", args[1])
    quit 1

main()
