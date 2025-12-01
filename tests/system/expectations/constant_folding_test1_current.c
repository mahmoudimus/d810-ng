// constant_folding_test1 - CURRENT OUTPUT (BROKEN)
// Address: 0x182c
// Generated: 2024-11-30
//
// STATUS: CATASTROPHIC FAILURE
// The deobfuscator turned a boolean-returning function into an infinite loop.
// Root cause: FixPredecessorOfConditionalJumpBlock applied 50 times,
// making all real blocks unreachable.

void constant_folding_test1()
{
    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

    while ( 1 )
        ;
}
