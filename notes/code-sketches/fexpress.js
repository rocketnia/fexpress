// fexpress.js

// Copyright (c) 2011 Ross Angle
//
//   Permission is hereby granted, free of charge, to any person
//   obtaining a copy of this software and associated documentation
//   files (the "Software"), to deal in the Software without
//   restriction, including without limitation the rights to use,
//   copy, modify, merge, publish, distribute, sublicense, and/or sell
//   copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following
//   conditions:
//
//   The above copyright notice and this permission notice shall be
//   included in all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
//   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
//   OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
//   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
//   HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
//   WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
//   OTHER DEALINGS IN THE SOFTWARE.
//
// Permission to use this software is also granted under the
// Perl Foundation's Artistic License 2.0. You may use either license,
// at your option.


// This depends on Lathe.js (https://github.com/rocketnia/lathe),
// which must be on the global variable "_".

// Fexpress is intended to be a programming language with partial
// evaluation and predictable performance. To this end, it should
// evaluate things extremely eagerly, even evaluating the bodies of
// function abstractions before they're called. In order to make this
// simple, nothing in Fexpress has side effects.
//
// Actually, right now fexpress's function abstraction just wraps its
// body expression in a data structure, making for a more traditional
// evaluation order. But the implementation is set up in a way that
// should make it straightforward to implement partial evaluation, and
// the language axioms are designed in a way that should make that
// partial evaluation pay off. Easy for me to say now, right?
//
// Fexpress uses fexprs that act as functions of the form
// "( unparsed argument list, caller's environment ) -> return value",
// like Kernel. Unlike Kernel, these are pure functions.
//
// Fexprs are a very simple way to breathe extensible meaning into a
// nearly meaningless but structured program representation. Either
// the program is a symbol whose meaning is determined by dictionary
// lookup, or it's a nonempty list of programs whose overall meaning
// is determined by the first program. In languages with macros,
// macroexpansion tends to work this way anyway, making those
// languages at least as complicated (albeit only if that phase is
// considered part of the language). In some sense, in an fexpr
// language, macroexpansion is all there is.


/*

Things with -- in front of them have been considered but aren't part of the implementation.

Eval[ Wrap[ Cons, rep ], env ] ==> Call[ Eval[ Get[ Car, rep ], env ], Get[ Cdr, rep ], env ]
Call[ Wrap[ Op, rep ], args, env ] ==>
  Eval[ Get[ Impl, rep ], Shadow[ Get[ BodyArg, rep ], args, Shadow[ Get[ EnvArg, rep ], env, Get[ LexicalEnv, rep ] ] ] ]

-- Unwrap[ type1, Wrap[ type2, rep ] ] where type1 is type2 ==> rep
Get[ key1, Shadow[ key2, val, rest ] ] where key1 is key2 ==> val
Get[ key1, Shadow[ key2, val, rest ] ] where key1 isn't key2 ==> Get[ key1, rest ]
-- Get[ key1, Shadow[ key2, val, rest ] ] ==> IfEq[ key1, key2, val, Get[ key1, rest ] ]
-- IfEq[ a, b, then, else ] where a is b ==> then
-- IfEq[ a, b, then, else ] where a is not b ==> else

Eval[ expr@Wrap[ String, rep ], env ] ==> Get[ expr, env ]

Shadow[ key1, val1, Shadow[ key2, val2, rest ] ] where key2 is less than key1 ==>
  Shadow[ key2, val2, Shadow[ key1, val1, rest ] ]
Shadow[ key1, val1, Shadow[ key2, val2, rest ] ] where key1 is key2 ==> Shadow[ key1, val1, rest ]

Call[ Vau, '(bodyarg envarg impl), env ] ==> Wrap[ Op, { LexicalEnv: env, BodyArg: 'bodyarg, EnvArg: 'envarg, Impl: 'impl } ]

*/


function KnownString( string ) {
    this.string_ = "" + string;
}

KnownString.prototype.toString = function () {
    return JSON.stringify( this.string_ );
};

function KnownWrap( type, rep ) {
    this.type_ = type;
    this.rep_ = rep;
}

KnownWrap.prototype.toString = function () {
    return "" + this.type_ + "::" + this.rep_;
};

function KnownMap( sortedEntries ) {
    this.sortedEntries_ = sortedEntries;
}

KnownMap.prototype.toString = function () {
    return this.sortedEntries_.length === 0 ? "{}" :
        "{ " + _.arrMap( this.sortedEntries_, function ( it ) {
            return "" + it[ 0 ] + ": " + it[ 1 ];
        } ).join( ", " ) + " }";
};

// TODO: Actually choose a particular order. This is just set up to
// ensure *some* order, not necessarily the nicest one. It does ensure
// that strings are in alphabetical order, so that our uses of
// wrapmapExpr already put their Shadow[ ... ] nesting in normal form.
function compareKnown( a, b ) {
    var as = [ a ], bs = [ b ];
    while ( as.length !== 0 ) {
        a = as.pop(), b = bs.pop();
        if ( a instanceof KnownString ) {
            if ( b instanceof KnownString ) {
                var astr = a.string_, bstr = b.string_;
                if ( astr !== bstr )
                    return astr < bstr ? -1 : 1;
            } else {
                return -1;
            }
        } else if ( b instanceof KnownString ) {
            return 1;
        } else if ( a instanceof KnownWrap ) {
            if ( b instanceof KnownWrap ) {
                as.push( a.type_, a.rep_ );
                bs.push( b.type_, b.rep_ );
            } else {
                return -1;
            }
        } else if ( b instanceof KnownWrap ) {
            return 1;
        } else {
            var aents = a.sortedEntries_, bents = b.sortedEntries_;
            var an = aents.length, bn = bents.length;
            if ( an !== bn )
                return an < bn ? -1 : 1;
            _.arrEach( aents, function ( it ) {
                as.push( it[ 0 ], it[ 1 ] );
            } );
            _.arrEach( bents, function ( it ) {
                bs.push( it[ 0 ], it[ 1 ] );
            } );
        }
    }
    return 0;
}

function PatternVar( name ) { this.name_ = name; }
function v( name ) { return new PatternVar( name ); }
function mat( expr, pattern ) {
    var results = {};
    function addResults( expr, pattern ) {
        if ( pattern instanceof PatternVar ) {
            results[ pattern.name_ ] = expr;
        } else if ( _.isString( pattern ) ) {
            if ( !(_.isString( expr ) && "" + expr === "" + pattern) )
                return void (results = null);
        } else if ( _.likeArray( pattern ) ) {
            var n = pattern.length;
            if ( !(_.likeArray( expr ) && expr.length === n) )
                return void (results = null);
            for ( var i = 0; i < n && results; i++ )
                addResults( expr[ i ], pattern[ i ] );
        } else {
            throw new Error();
        }
    }
    addResults( expr, pattern );
    return results && function ( name ) { return results[ name ]; };
}

function known( expr ) {
    var done = false, hasResult = false, result = null;
    var endResult;
    function ret( result ) {
        done = true;
        endResult = result;
    }
    while ( !done ) {
        var m;
        if ( _.isString( expr ) ) {
            hasResult = true, result = new KnownString( expr );
        } else if ( m = mat( expr, [ "Wrap", v( "type" ), v( "rep" ) ] ) )
        (function () {  // local scope
            var type = m( "type" ), rep = m( "rep" );
            var oldRet = ret;
            expr = type; ret = function ( knownType ) {
            if ( knownType === null )
                return void (hasResult = true, result = null, ret = oldRet);
            expr = rep; ret = function ( knownRep ) {
            if ( knownRep === null )
                return void (hasResult = true, result = null, ret = oldRet);
            hasResult = true, result = new KnownWrap( knownType, knownRep );
            ret = oldRet; }; };
        })();
        else if ( mat( expr, [ "EmptyMap" ] ) ) {
            hasResult = true, result = new KnownMap( [] );
        } else if ( m = mat( expr, [ "Shadow", v( "key" ), v( "val" ), v( "rest" ) ] ) )
        (function () {  // local scope
            var key = m( "key" ), val = m( "val" ), rest = m( "rest" );
            var oldRet = ret;
            expr = key; ret = function ( knownKey ) {
            if ( knownKey === null )
                return void (hasResult = true, result = null, ret = oldRet);
            expr = val; ret = function ( knownVal ) {
            if ( knownVal === null )
                return void (hasResult = true, result = null, ret = oldRet);
            // TODO: Stop requiring the rest to be fully known. If a
            // key with a known value shadows a key with an unknown
            // value, the result should be known.
            expr = rest; ret = function ( knownRest ) {
            if ( knownRest instanceof KnownMap ) {
                var entries = []; 
                // TODO: Represent sortedEntries_ as a heap, or at
                // least do a binary search here.
                var hasOurs = false;
                _.arrEach( knownRest.sortedEntries_, function ( entry ) {
                    if ( hasOurs )
                        return void entries.push( entry );
                    var compared = compareKnown( knownKey, entry[ 0 ] );
                    if ( compared <= 0 ) {
                        entries.push( [ knownKey, knownVal ] );
                        hasOurs = true;
                    }
                    if ( compared !== 0 )
                        entries.push( entry );
                } );
                if ( !hasOurs )
                    entries.push( [ knownKey, knownVal ] );
                hasResult = true, result = new KnownMap( entries );
                ret = oldRet;
            } else {
                hasResult = true, result = null, ret = oldRet;
            }
            }; }; };
        })();
        else {
            hasResult = true, result = null;
        }
        while ( hasResult ) {
            var resultWas = result;
            hasResult = false, result = null;
            ret( resultWas );
        }
    }
    return endResult;
}

function mapExprArray( args ) {
    var result = [ "EmptyMap" ];
    for ( var i = args.length - 1; 0 <= i; i -= 2 )
        result = [ "Shadow", args[ i - 1 ], args[ i ], result ];
    return result;
}

function mapExpr( var_args ) {
    return mapExprArray( arguments );
}

function wrapmapExpr( type, var_args ) {
    return [ "Wrap", type, mapExprArray( _.arrCut( arguments, 1 ) ) ];
}

function listExprArray( args ) {
    var result = wrapmapExpr( "Nil" );
    for ( var i = args.length - 1; 0 <= i; i-- ) {
        // NOTE: The order of fields matters here, so that the
        // Shadow[ ... ] nesting is in normal form.
        result =
            wrapmapExpr( "Cons", "Car", args[ i ], "Cdr", result );
    }
    return result;
}

function listExpr( var_args ) {
    return listExprArray( arguments );
}

function specializeOneLevel( expr ) {
    var done = false;
    function step( result ) {
        done = true;
    }
    while ( !done ) {
        while ( true ) {
            var m, key1, key2;
            if ( m = mat( expr, [ "Eval", [ "Wrap", "Cons", v( "rep" ) ], v( "env" ) ] ) )
            (function () {  // local scope
// Eval[ Wrap[ Cons, rep ], env ] ==> Call[ Eval[ Get[ Car, rep ], env ], Get[ Cdr, rep ], env ]
                var rep = m( "rep" ), env = m( "env" );
                var oldStep = step;
                expr = [ "Get", "Car", rep ]; step = function ( opExpr ) {
                expr = [ "Eval", opExpr, env ]; step = function ( op ) {
                expr = [ "Get", "Cdr", rep ]; step = function ( args ) {
                expr = [ "Call", op, args, env ];
                step = oldStep; }; }; };
            })();
            else if ( m = mat( expr, [ "Call", [ "Wrap", "Op", v( "rep" ) ], v( "args" ), v( "env" ) ] ) )
            (function () {  // local scope
// Call[ Wrap[ Op, rep ], args, env ] ==>
//   Eval[ Get[ Impl, rep ], Shadow[ Get[ BodyArg, rep ], args, Shadow[ Get[ EnvArg, rep ], env, Get[ LexicalEnv, rep ] ] ] ]
                var rep = m( "rep" ), args = m( "args" ), env = m( "env" );
                var oldStep = step;
                expr = [ "Get", "Impl", rep ]; step = function ( impl ) {
                expr = [ "Get", "BodyArg", rep ]; step = function ( bodyArg ) {
                expr = [ "Get", "EnvArg", rep ]; step = function ( envArg ) {
                expr = [ "Get", "LexicalEnv", rep ]; step = function ( lexicalEnv ) {
                expr = [ "Shadow", envArg, env, lexicalEnv ]; step = function ( halfLocalEnv ) {
                expr = [ "Shadow", bodyArg, args, halfLocalEnv ]; step = function ( localEnv ) {
                expr = [ "Eval", impl, localEnv ];
                step = oldStep; }; }; }; }; }; };
            })();
            // TODO: Oops, this shouldn't need key1 and key2 to be completely known, just known enough.
            else if ( (m = mat( expr, [ "Get", v( "key1" ), [ "Shadow", v( "key2" ), v( "val" ), v( "rest" ) ] ] ))
                && (key1 = known( m( "key1" ) )) !== null
                && (key2 = known( m( "key2" ) )) !== null ) {
// Get[ key1, Shadow[ key2, val, rest ] ] where key1 is key2 ==> val
// Get[ key1, Shadow[ key2, val, rest ] ] where key1 isn't key2 ==> Get[ key1, rest ]
                var compared = compareKnown( key1, key2 );
                expr = compared === 0 ? m( "val" ) : [ "Get", m( "key1" ), m( "rest" ) ];
            } else if ( (m = mat( expr, [ "Eval", v( "expr" ), v( "env" ) ] ))
                && mat( m( "expr" ), [ "Wrap", "String", v( "rep" ) ] ) ) {
// Eval[ expr@Wrap[ String, rep ], env ] ==> Get[ expr, env ]
                expr = [ "Get", m( "expr" ), m( "env" ) ];
            // TODO: Oops, this shouldn't need key1 and key2 to be completely known, just known enough.
            } else if ( (m = mat( expr, [ "Shadow", v( "key1" ), v( "val1" ), [ "Shadow", v( "key2" ), v( "val2" ), v( "rest" ) ] ] ))
                && (key1 = known( m( "key1" ) )) !== null
                && (key2 = known( m( "key2" ) )) !== null
                && compareKnown( key2, key1 ) < 0 )
            (function () {  // local scope
// Shadow[ key1, val1, Shadow[ key2, val2, rest ] ] where key2 is less than key1 ==>
//   Shadow[ key2, val2, Shadow[ key1, val1, rest ] ]
                var key2 = m( "key2" ), val2 = m( "val2" );
                var oldStep = step;
                expr = [ "Shadow", m( "key1" ), m( "val1" ), m( "rest" ) ]; step = function ( halfRest ) {
                expr = [ "Shadow", key2, val2, halfRest ];
                step = oldStep; };
            })();
            // TODO: Oops, this shouldn't need key1 and key2 to be completely known, just known enough.
            else if ( (m = mat( expr, [ "Shadow", v( "key1" ), v( "val1" ), [ "Shadow", v( "key2" ), v( "val2" ), v( "rest" ) ] ] ))
                && (key1 = known( m( "key1" ) )) !== null
                && (key2 = known( m( "key2" ) )) !== null
                && compareKnown( key1, key2 ) === 0 ) {
// Shadow[ key1, val1, Shadow[ key2, val2, rest ] ] where key1 is key2 ==> Shadow[ key1, val1, rest ]
                expr = [ "Shadow", m( "key1" ), m( "val1" ), m( "rest" ) ];
            // TODO: Instead of capturing the lexically enclosing environment, this should partially evaluate its body based on that environment, with unknowns in place of the bodyarg and envarg.
            } else if ( m = mat( expr, [ "Call", "Vau", listExpr( v( "bodyarg" ), v( "envarg" ), v( "impl" ) ), v( "env" ) ] ) ) {
// Call[ Vau, '(bodyarg envarg impl), env ] ==> Wrap[ Op, { LexicalEnv: env, BodyArg: 'bodyarg, EnvArg: 'envarg, Impl: 'impl } ]
                // NOTE: The order of fields matters here, so that the Shadow[ ... ] nesting is in normal form.
                expr = wrapmapExpr( "Op", "BodyArg", m( "bodyarg" ), "EnvArg", m( "envarg" ), "Impl", m( "impl" ), "LexicalEnv", m( "env" ) );
            } else {
                break;
            }
        }
        step( expr );
    }
    return expr;
}

// Test cases (all passing!):
//
// mat( specializeOneLevel( [ "Shadow", [ "Wrap", "String", "Woo" ], "Hoo", [ "Shadow", [ "Wrap", "String", "Coo" ], "Hoo", [ "Shadow", [ "Wrap", "String", "Boo" ], "Hoo", [ "EmptyMap" ] ] ] ] ),
//     [ "Shadow", [ "Wrap", "String", "Boo" ], "Hoo", [ "Shadow", [ "Wrap", "String", "Coo" ], "Hoo", [ "Shadow", [ "Wrap", "String", "Woo" ], "Hoo", [ "EmptyMap" ] ] ] ] )
//
// mat( specializeOneLevel( [ "Shadow", [ "Wrap", "String", "Woo" ], "Hoo", [ "Shadow", [ "Wrap", "String", "Woo" ], "Boo", [ "EmptyMap" ] ] ] ),
//     [ "Shadow", [ "Wrap", "String", "Woo" ], "Hoo", [ "EmptyMap" ] ] )
//
// mat( specializeOneLevel( [ "Eval", [ "Wrap", "String", "Woo" ], [ "Shadow", [ "Wrap", "String", "Woo" ], "Hoo", [ "EmptyMap" ] ] ] ),
//     "Hoo" )
//
// mat( specializeOneLevel( [ "Eval", listExpr( [ "Wrap", "String", "Woo" ], "X", "Y", "Z" ), [ "Shadow", [ "Wrap", "String", "Woo" ], "Vau", [ "EmptyMap" ] ] ] ),
//     [ "Wrap", "Op", [ "Shadow", "BodyArg", "X", [ "Shadow", "EnvArg", "Y", [ "Shadow", "Impl", "Z", [ "Shadow", "LexicalEnv", [ "Shadow", [ "Wrap", "String", "Woo" ], "Vau", [ "EmptyMap" ] ], [ "EmptyMap" ] ] ] ] ] ] )

