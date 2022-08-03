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
    s/import qualified Prelude$/$imports/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/'\\000'/0/g;

    s/Exp.Capability p v _ _ e0 e1 e2/Exp.Capability p v e0 e1 e2/;
    s/Exp.WithCapability p v (_UU[0-9a-f]+_) _ e0 e1 e2 e3 e4/Exp.WithCapability p v $1 e0 e1 e2 e3 e4/;
    s/Exp.ComposeCapability p v _ e0 e1 e2 e3/Exp.ComposeCapability p v e0 e1 e2 e3/;

    # next if /^emptyDSL ::/ .. /^$/;

    print;
}
