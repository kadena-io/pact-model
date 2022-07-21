#!/usr/bin/env perl

$imports = <<'END_IMPORTS';
import qualified Util.HString as HString
import qualified Data.Char
import qualified Data.Function
import qualified Data.List
import qualified Data.Maybe
import qualified Data.Ratio
import qualified Data.Word
import qualified Prelude
import qualified System.IO.Unsafe
END_IMPORTS

while (<>) {
    s/import qualified Prelude/$imports/;
    s/module (.+?) where/module Pact.$1 where/ unless /module Pact/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/'\\000'/0/g;

    # next if /^emptyDSL ::/ .. /^$/;

    print;
}
