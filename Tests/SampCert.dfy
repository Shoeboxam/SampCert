
module {:extern} Random {

  class {:extern} Random {

    static method {:extern "UniformPowerOfTwoSample"} ExternUniformPowerOfTwoSample(n: nat) returns (u: nat)

  }

}

module {:extern} SampCert {

  import Random

  type pos = x: nat | x > 0 witness 1

  class SLang {


    method UniformPowerOfTwoSample(n: nat) returns (u: nat)

      requires n >= 1

    {

      u := Random.Random.ExternUniformPowerOfTwoSample(n);

    }
    method {:verify false} UniformSample (n: pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      var x := UniformPowerOfTwoSample(2 * n);
      while ! (x < n)
        decreases *
      {
        x := UniformPowerOfTwoSample(2 * n, x);
      }
      var r := x;
      o := r;
    }

    method {:verify false} UniformPowerOfTwoSample (n: pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      o := probUniformP2(2 log n);
    }

    method {:verify false} BernoulliSample (num: nat, den: pos)
      returns (o: bool)
      requires num <= den 
      modifies this
      decreases *
    {
      var d := UniformSample(den);
      o := d < num;
    }

    method {:verify false} BernoulliExpNegSampleUnitLoop (num: nat, den: pos, state: (bool,pos))
      returns (o: (bool,pos))
      requires num <= den 
      modifies this
      decreases *
    {
      var A := BernoulliSample(num, state.1 * den);
      o := (A,state.1 + 1);
    }

    method {:verify false} BernoulliExpNegSampleUnitAux (num: nat, den: pos)
      returns (o: nat)
      requires num <= den 
      modifies this
      decreases *
    {
      var state := (true,1);
      while state.0
        decreases *
      {
        state := BernoulliExpNegSampleUnitLoop(num, den, state);
      }
      var r := state;
      o := r.1;
    }

    method {:verify false} BernoulliExpNegSampleUnit (num: nat, den: pos)
      returns (o: bool)
      requires num <= den 
      modifies this
      decreases *
    {
      var K := BernoulliExpNegSampleUnitAux(num, den);
      if K % 2 == 0 {
        o := true;
      } else {
        o := false;
      }
    }

    method {:verify false} BernoulliExpNegSampleGenLoop (iter: nat)
      returns (o: bool)
      modifies this
      decreases *
    {
      if iter == 0 {
        o := true;
      } else {
        var B := BernoulliExpNegSampleUnit(1, 1);
        if ! (B == true) {
          o := B;
        } else {
          var R := BernoulliExpNegSampleGenLoop(iter - 1);
          o := R;
        }
      }
    }

    method {:verify false} BernoulliExpNegSample (num: nat, den: pos)
      returns (o: bool)
      modifies this
      decreases *
    {
      if num <= den {
        var X := BernoulliExpNegSampleUnit(num, den);
        o := X;
      } else {
        var gamf := num / den;
        var B := BernoulliExpNegSampleGenLoop(gamf);
        if B == true {
          var X := BernoulliExpNegSampleUnit(num % den, den);
          o := X;
        } else {
          o := false;
        }
      }
    }

    method {:verify false} DiscreteLaplaceSampleLoopIn1Aux (t: pos)
      returns (o: (nat,bool))
      modifies this
      decreases *
    {
      var U := UniformSample(t);
      var D := BernoulliExpNegSample(U, t);
      o := (U,D);
    }

    method {:verify false} DiscreteLaplaceSampleLoopIn1 (t: pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      var x := DiscreteLaplaceSampleLoopIn1Aux(t);
      while ! (x.1)
        decreases *
      {
        x := DiscreteLaplaceSampleLoopIn1Aux(t, x);
      }
      var r1 := x;
      o := r1.0;
    }

    method {:verify false} DiscreteLaplaceSampleLoopIn2Aux (num: nat, den: pos, K: (bool,nat))
      returns (o: (bool,nat))
      modifies this
      decreases *
    {
      var A := BernoulliExpNegSample(num, den);
      o := (A,K.1 + 1);
    }

    method {:verify false} DiscreteLaplaceSampleLoopIn2 (num: nat, den: pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      var K := (true,0);
      while K.0
        decreases *
      {
        K := DiscreteLaplaceSampleLoopIn2Aux(num, den, K);
      }
      var r2 := K;
      o := r2.1;
    }

    method {:verify false} DiscreteLaplaceSampleLoop (num: pos, den: pos)
      returns (o: (bool,nat))
      modifies this
      decreases *
    {
      var v := DiscreteLaplaceSampleLoopIn2(den, num);
      var V := v - 1;
      var B := BernoulliSample(1, 2);
      o := (B,V);
    }

    method {:verify false} DiscreteLaplaceSampleLoop' (num: pos, den: pos)
      returns (o: (bool,nat))
      modifies this
      decreases *
    {
      var U := DiscreteLaplaceSampleLoopIn1(num);
      var v := DiscreteLaplaceSampleLoopIn2(1, 1);
      var V := v - 1;
      var X := U + num * V;
      var Y := X / den;
      var B := BernoulliSample(1, 2);
      o := (B,Y);
    }

    method {:verify false} DiscreteLaplaceSample (num: pos, den: pos)
      returns (o: int)
      modifies this
      decreases *
    {
      var x := DiscreteLaplaceSampleLoop(num, den);
      while ! (! (x.0 == true && x.1 == 0))
        decreases *
      {
        x := DiscreteLaplaceSampleLoop(num, den, x);
      }
      var r := x;
      var Z := if r.0 == true then - (r.1) else r.1;
      o := Z;
    }

    method {:verify false} DiscreteLaplaceSampleOptimized (num: pos, den: pos)
      returns (o: int)
      modifies this
      decreases *
    {
      var x := DiscreteLaplaceSampleLoop'(num, den);
      while ! (! (x.0 == true && x.1 == 0))
        decreases *
      {
        x := DiscreteLaplaceSampleLoop'(num, den, x);
      }
      var r := x;
      var Z := if r.0 == true then - (r.1) else r.1;
      o := Z;
    }

    method {:verify false} DiscreteLaplaceSampleMixed (num: pos, den: pos, mix: nat)
      returns (o: int)
      modifies this
      decreases *
    {
      if num <= den * mix {
        var v := DiscreteLaplaceSample(num, den);
        o := v;
      } else {
        var v := DiscreteLaplaceSampleOptimized(num, den);
        o := v;
      }
    }

    method {:verify false} DiscreteGaussianSampleLoop (num: pos, den: pos, t: pos, mix: nat)
      returns (o: (int,bool))
      modifies this
      decreases *
    {
      var Y := DiscreteLaplaceSampleMixed(t, 1, mix);
      var y := (if Y < 0 then -(Y) else (Y));
      var n := ((if y * t * den - num < 0 then -(y * t * den - num) else (y * t * den - num))) * ((if y * t * den - num < 0 then -(y * t * den - num) else (y * t * den - num)));
      var d := 2 * num * (t) * (t) * den;
      var C := BernoulliExpNegSample(n, d);
      o := (Y,C);
    }

    method {:verify false} DiscreteGaussianSample (num: pos, den: pos, mix: nat)
      returns (o: int)
      modifies this
      decreases *
    {
      var ti := num / den;
      var t := ti + 1;
      var num := (num) * (num);
      var den := (den) * (den);
      var x := DiscreteGaussianSampleLoop(num, den, t, mix);
      while ! (x.1)
        decreases *
      {
        x := DiscreteGaussianSampleLoop(num, den, t, mix, x);
      }
      var r := x;
      o := r.0;
    }

    method {:verify false} PermuteAndFlipSample (n: nat, q: seq<nat>, ε₁: nat, ε₂: pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      var mask := PermuteAndFlipFullMask(n);
      o := PermuteAndFlipSampleCore(n, q, ε₁, ε₂, mask, n + 1);
    }

    method {:verify false} PermuteAndFlipFullMask (n: nat)
      returns (o: nat)
      modifies this
      decreases *
    {
      if n == 0 {
        o := 1;
      } else {
        var mask := PermuteAndFlipFullMask(n - 1);
        o := 2 * mask + 1;
      }
    }

    method {:verify false} PermuteAndFlipSampleCore (n: nat, q: seq<nat>, ε₁: nat, ε₂: pos, mask: nat, rem: nat)
      returns (o: nat)
      modifies this
      decreases *
    {
      var state := (false,(0,(mask,rem)));
      while ! (state.0 == true)
        decreases *
      {
        state := PermuteAndFlipSampleLoop(n, q, ε₁, ε₂, state);
      }
      var st := state;
      o := st.1.0;
    }

    method {:verify false} PermuteAndFlipSampleLoop (n: nat, q: seq<nat>, ε₁: nat, ε₂: pos, state: (bool,(nat,(nat,nat))))
      returns (o: (bool,(nat,(nat,nat))))
      modifies this
      decreases *
    {
      var result := state.1.0;
      var mask := state.1.1.0;
      var rem := state.1.1.1;
      if rem == 0 {
        o := (true,(result,(mask,rem)));
      } else {
        var k := UniformSample(rem);
        var i := PermuteAndFlipKthActive(n, mask, k);
        var g := PermuteAndFlipGap(n, q, i);
        var accept := BernoulliExpNegSample(g * ε₁, ε₂);
        if accept == true {
          o := (true,(i,(mask,rem)));
        } else {
          var mask' := PermuteAndFlipClearBit(n, mask, i);
          o := (false,(result,(mask',rem - 1)));
        }
      }
    }

    method {:verify false} PermuteAndFlipKthActive (n: nat, mask: nat, k: nat)
      returns (o: nat)
      modifies this
      decreases *
    {
      var state := (false,(k,(0,n + 1)));
      while ! (state.0 == true)
        decreases *
      {
        state := PermuteAndFlipKthActiveLoop(n, mask, state);
      }
      var st := state;
      o := st.1.1.0;
    }

    method {:verify false} PermuteAndFlipKthActiveLoop (n: nat, mask: nat, state: (bool,(nat,(nat,nat))))
      returns (o: (bool,(nat,(nat,nat))))
      modifies this
      decreases *
    {
      var k := state.1.0;
      var found := state.1.1.0;
      var rem := state.1.1.1;
      if rem == 0 {
        o := (true,(k,(found,rem)));
      } else {
        var curr := n + 1 - rem;
        var i := curr;
        var active := PermuteAndFlipHasBit(mask, curr);
        if active == true {
          if k == 0 {
            o := (true,(k,(i,rem)));
          } else {
            o := (false,(k - 1,(found,rem - 1)));
          }
        } else {
          o := (false,(k,(found,rem - 1)));
        }
      }
    }

    method {:verify false} PermuteAndFlipHasBit (mask: nat, i: nat)
      returns (o: bool)
      modifies this
      decreases *
    {
      var p := PermuteAndFlipPow2(i);
      o := mask / p % 2 == 1;
    }

    method {:verify false} PermuteAndFlipPow2 (n: nat)
      returns (o: nat)
      modifies this
      decreases *
    {
      if n == 0 {
        o := 1;
      } else {
        var p := PermuteAndFlipPow2(n - 1);
        o := 2 * p;
      }
    }

    method {:verify false} PermuteAndFlipGap (n: nat, q: seq<nat>, target: nat)
      returns (o: nat)
      modifies this
      decreases *
    {
      var state := (0,n + 1);
      while state.1 != 0
        decreases *
      {
        state := PermuteAndFlipGapLoop(n, q, target, state);
      }
      var st := state;
      o := st.0;
    }

    method {:verify false} PermuteAndFlipGapLoop (n: nat, q: seq<nat>, target: nat, state: (nat,nat))
      returns (o: (nat,nat))
      modifies this
      decreases *
    {
      var best := state.0;
      var rem := state.1;
      if rem == 0 {
        o := state;
      } else {
        var curr := n + 1 - rem;
        var i := curr;
        var cand := q[i] - q[target];
        var best' := if best < cand then cand else best;
        o := (best',rem - 1);
      }
    }

    method {:verify false} PermuteAndFlipClearBit (n: nat, mask: nat, i: nat)
      returns (o: nat)
      modifies this
      decreases *
    {
      var p := PermuteAndFlipPow2(i);
      var active := PermuteAndFlipHasBit(mask, i);
      if active == true {
        o := mask - p;
      } else {
        o := mask;
      }
    }


}

}
