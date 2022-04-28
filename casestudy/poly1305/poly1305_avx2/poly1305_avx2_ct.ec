require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel Leakage_models.

require import Array2 Array3 Array4 Array5.
require import WArray16 WArray24 WArray64 WArray96 WArray128 WArray160.

abbrev bit25_u64 = W64.of_int 16777216.


abbrev mask26_u64 = W64.of_int 67108863.


abbrev five_u64 = W64.of_int 5.


abbrev zero_u64 = W64.of_int 0.

theory T.
clone import ALeakageModel as LeakageModel.

module M = {
  var leakages : leakages_t

  proc load2 (p:W64.t) : W64.t Array2.t = {
    var aux: W64.t;

    var x:W64.t Array2.t;
    x <- witness;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 0))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))));
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 8))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))));
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    return (x);
  }

  proc load_add (h:W64.t Array3.t, in_0:W64.t) : W64.t Array3.t = {
    var aux: bool;
    var aux_0: W64.t;

    var cf:bool;
    var  _0:bool;

    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 0))))]
                         ++ [0]) :: leakages;
    (aux, aux_0) <- adc_64 h.[0]
    (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0)))) false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 8))))]
                         ++ [1]) :: leakages;
    (aux, aux_0) <- adc_64 h.[1]
    (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int 8)))) cf;
    cf <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux, aux_0) <- adc_64 h.[2] (W64.of_int 1) cf;
     _0 <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    return (h);
  }

  proc load_last_add (h:W64.t Array3.t, in_0:W64.t, len:W64.t) : W64.t Array3.t = {
    var aux_1: bool;
    var aux_0: W8.t;
    var aux: W64.t;

    var s:W64.t Array2.t;
    var j:W64.t;
    var c:W8.t;
    var cf:bool;
    var  _0:bool;
    s <- witness;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    s.[0] <- aux;
    aux <- (W64.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    s.[1] <- aux;
    aux <- (W64.of_int 0);
    j <- aux;

    leakages <- LeakCond((j \ult len)) :: LeakAddr([]) :: leakages;

    while ((j \ult len)) {
      leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + j)))]) :: leakages;
      aux_0 <- (loadW8 Glob.mem (W64.to_uint (in_0 + j)));
      c <- aux_0;
      aux_0 <- c;
      leakages <- LeakAddr([(W64.to_uint j)]) :: leakages;
      s <-
      Array2.init
      (WArray16.get64 (WArray16.set8 (WArray16.init64 (fun i => s.[i])) (W64.to_uint j) aux_0));
      aux <- (j + (W64.of_int 1));
      j <- aux;
    leakages <- LeakCond((j \ult len)) :: LeakAddr([]) :: leakages;

    }
    aux_0 <- (W8.of_int 1);
    leakages <- LeakAddr([(W64.to_uint j)]) :: leakages;
    s <-
    Array2.init
    (WArray16.get64 (WArray16.set8 (WArray16.init64 (fun i => s.[i])) (W64.to_uint j) aux_0));
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    (aux_1, aux) <- adc_64 h.[0] s.[0] false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    (aux_1, aux) <- adc_64 h.[1] s.[1] cf;
    cf <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux) <- adc_64 h.[2] (W64.of_int 0) cf;
     _0 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    return (h);
  }

  proc store2 (p:W64.t, x:W64.t Array2.t) : unit = {
    var aux: W64.t;



    leakages <- LeakAddr([0]) :: leakages;
    aux <- x.[0];
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 0))))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 0))) aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- x.[1];
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (p + (W64.of_int 8))))]) :: leakages;
    Glob.mem <- storeW64 Glob.mem (W64.to_uint (p + (W64.of_int 8))) aux;
    return ();
  }

  proc clamp (k:W64.t) : W64.t Array3.t = {
    var aux: W64.t;

    var r:W64.t Array3.t;
    r <- witness;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (k + (W64.of_int 0))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (k + (W64.of_int 0))));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (k + (W64.of_int 8))))]) :: leakages;
    aux <- (loadW64 Glob.mem (W64.to_uint (k + (W64.of_int 8))));
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (r.[0] `&` (W64.of_int 1152921487695413247));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (r.[1] `&` (W64.of_int 1152921487695413244));
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- r.[1];
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (r.[2] `>>` (W8.of_int 2));
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux;
    leakages <- LeakAddr([1] ++ [2]) :: leakages;
    aux <- (r.[2] + r.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux;
    return (r);
  }

  proc add2 (h:W64.t Array2.t, s:W64.t Array2.t) : W64.t Array2.t = {
    var aux: bool;
    var aux_0: W64.t;

    var cf:bool;
    var  _0:bool;

    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    (aux, aux_0) <- adc_64 h.[0] s.[0] false;
    cf <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    (aux, aux_0) <- adc_64 h.[1] s.[1] cf;
     _0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    return (h);
  }

  proc mulmod (h:W64.t Array3.t, r:W64.t Array3.t) : W64.t Array3.t = {
    var aux_1: bool;
    var aux_0: W64.t;
    var aux: W64.t;

    var t2:W64.t;
    var rax:W64.t;
    var rdx:W64.t;
    var t0:W64.t;
    var t1:W64.t;
    var cf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;

    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- r.[2];
    t2 <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (t2 * h.[2]);
    t2 <- aux_0;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux_0 <- (h.[2] * r.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r.[0];
    rax <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[0];
    rdx <- aux_0;
    rax <- aux;
    aux_0 <- rax;
    t0 <- aux_0;
    aux_0 <- rdx;
    t1 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- r.[0];
    rax <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[1];
    rdx <- aux_0;
    rax <- aux;
    (aux_1, aux_0) <- adc_64 t1 rax false;
    cf <- aux_1;
    t1 <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[2] rdx cf;
     _0 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- r.[2];
    rax <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[1];
    rdx <- aux_0;
    rax <- aux;
    aux_0 <- rdx;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- (h.[1] + t2);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    aux_0 <- rax;
    t2 <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- r.[1];
    rax <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- mulu_64 rax h.[0];
    rdx <- aux_0;
    rax <- aux;
    (aux_1, aux_0) <- adc_64 t0 t2 false;
    cf <- aux_1;
    t0 <- aux_0;
    (aux_1, aux_0) <- adc_64 t1 rax cf;
    cf <- aux_1;
    t1 <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[2] rdx cf;
     _1 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    aux_0 <- (W64.of_int 18446744073709551612);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- h.[2];
    t2 <- aux_0;
    aux_0 <- (t2 `>>` (W8.of_int 2));
    t2 <- aux_0;
    leakages <- LeakAddr([2] ++ [0]) :: leakages;
    aux_0 <- (h.[0] `&` h.[2]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- (h.[0] + t2);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    aux_0 <- (h.[2] `&` (W64.of_int 3));
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[0] t0 false;
    cf <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[1] t1 cf;
    cf <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_1, aux_0) <- adc_64 h.[2] (W64.of_int 0) cf;
     _2 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux_0;
    return (h);
  }

  proc freeze (h:W64.t Array3.t) : W64.t Array2.t = {
    var aux_0: bool;
    var aux: W64.t;

    var g:W64.t Array2.t;
    var g2:W64.t;
    var cf:bool;
    var mask:W64.t;
    var  _0:bool;
    g <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- h.[0];
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- h.[1];
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- h.[2];
    g2 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- adc_64 g.[0] (W64.of_int 5) false;
    cf <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_0, aux) <- adc_64 g.[1] (W64.of_int 0) cf;
    cf <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    (aux_0, aux) <- adc_64 g2 (W64.of_int 0) cf;
     _0 <- aux_0;
    g2 <- aux;
    aux <- (g2 `>>` (W8.of_int 2));
    g2 <- aux;
    aux <- (- g2);
    mask <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (g.[0] `^` h.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (g.[1] `^` h.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (g.[0] `&` mask);
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (g.[1] `&` mask);
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (g.[0] `^` h.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    g.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (g.[1] `^` h.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    g.[1] <- aux;
    return (g);
  }

  proc poly1305_ref3_setup (k:W64.t) : W64.t Array3.t * W64.t Array3.t *
                                       W64.t = {
    var aux: int;
    var aux_0: W64.t;
    var aux_1: W64.t Array3.t;

    var h:W64.t Array3.t;
    var r:W64.t Array3.t;
    var i:int;
    h <- witness;
    r <- witness;
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 3) {
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      h.[i] <- aux_0;
      i <- i + 1;
    }
    aux_1 <@ clamp (k);
    r <- aux_1;
    aux_0 <- (k + (W64.of_int 16));
    k <- aux_0;
    return (h, r, k);
  }

  proc poly1305_ref3_update (in_0:W64.t, inlen:W64.t, h:W64.t Array3.t,
                             r:W64.t Array3.t) : W64.t * W64.t *
                                                 W64.t Array3.t = {
    var aux_0: W64.t;
    var aux: W64.t Array3.t;




    leakages <- LeakCond(((W64.of_int 16) \ule inlen)) :: LeakAddr([]) :: leakages;

    while (((W64.of_int 16) \ule inlen)) {
      aux <@ load_add (h, in_0);
      h <- aux;
      aux <@ mulmod (h, r);
      h <- aux;
      aux_0 <- (in_0 + (W64.of_int 16));
      in_0 <- aux_0;
      aux_0 <- (inlen - (W64.of_int 16));
      inlen <- aux_0;
    leakages <- LeakCond(((W64.of_int 16) \ule inlen)) :: LeakAddr([]) :: leakages;

    }
    return (in_0, inlen, h);
  }

  proc poly1305_ref3_last (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t,
                           h:W64.t Array3.t, r:W64.t Array3.t) : unit = {
    var aux_0: W64.t Array2.t;
    var aux: W64.t Array3.t;

    var h2:W64.t Array2.t;
    var s:W64.t Array2.t;
    h2 <- witness;
    s <- witness;
    leakages <- LeakCond(((W64.of_int 0) \ult inlen)) :: LeakAddr([]) :: leakages;
    if (((W64.of_int 0) \ult inlen)) {
      aux <@ load_last_add (h, in_0, inlen);
      h <- aux;
      aux <@ mulmod (h, r);
      h <- aux;
    } else {

    }
    aux_0 <@ freeze (h);
    h2 <- aux_0;
    aux_0 <@ load2 (k);
    s <- aux_0;
    aux_0 <@ add2 (h2, s);
    h2 <- aux_0;
    store2 (out, h2);
    return ();
  }

  proc poly1305_ref3_local (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    var aux_2: W64.t;
    var aux_1: W64.t;
    var aux_0: W64.t Array3.t;
    var aux: W64.t Array3.t;

    var h:W64.t Array3.t;
    var r:W64.t Array3.t;
    var len:W64.t;
    h <- witness;
    r <- witness;
    (aux_0, aux, aux_2) <@ poly1305_ref3_setup (k);
    h <- aux_0;
    r <- aux;
    k <- aux_2;
    aux_2 <- inlen;
    len <- aux_2;
    (aux_2, aux_1, aux_0) <@ poly1305_ref3_update (in_0, len, h, r);
    in_0 <- aux_2;
    len <- aux_1;
    h <- aux_0;
    poly1305_ref3_last (out, in_0, len, k, h, r);
    return ();
  }

  proc times_5 (r1234:W256.t Array5.t) : W256.t Array4.t = {
    var aux_0: int;
    var aux: W256.t;

    var r1234x5:W256.t Array4.t;
    var five:W256.t;
    var i:int;
    var t:W256.t;
    r1234x5 <- witness;
    aux <- VPBROADCAST_4u64 five_u64;
    five <- aux;
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([(1 + i)]) :: leakages;
      aux <- VPMULU_256 five r1234.[(1 + i)];
      t <- aux;
      aux <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r1234x5.[i] <- aux;
      i <- i + 1;
    }
    return (r1234x5);
  }

  proc broadcast_r4 (r1234:W256.t Array5.t, r1234x5:W256.t Array4.t) :
  W256.t Array5.t * W256.t Array4.t = {
    var aux: int;
    var aux_0: W256.t;

    var r4444:W256.t Array5.t;
    var r4444x5:W256.t Array4.t;
    var i:int;
    var t:W256.t Array5.t;
    r4444 <- witness;
    r4444x5 <- witness;
    t <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      leakages <- LeakAddr([(4 * i)]) :: leakages;
      aux_0 <- VPBROADCAST_4u64 (get64
                                (WArray160.init256 (fun i => r1234.[i]))
                                (4 * i));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- t.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r4444.[i] <- aux_0;
      i <- i + 1;
    }
    leakages <- LeakFor(0,4) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 4) {
      leakages <- LeakAddr([(4 * i)]) :: leakages;
      aux_0 <- VPBROADCAST_4u64 (get64
                                (WArray128.init256 (fun i => r1234x5.[i]))
                                (4 * i));
      leakages <- LeakAddr([i]) :: leakages;
      t.[i] <- aux_0;
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- t.[i];
      leakages <- LeakAddr([i]) :: leakages;
      r4444x5.[i] <- aux_0;
      i <- i + 1;
    }
    return (r4444, r4444x5);
  }

  proc poly1305_avx2_setup (r:W64.t Array3.t) : W256.t Array5.t *
                                                W256.t Array4.t *
                                                W256.t Array5.t *
                                                W256.t Array4.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_0: W64.t;
    var aux_6: W64.t Array3.t;
    var aux_7: W256.t Array4.t;
    var aux_8: W256.t Array5.t;

    var r4444:W256.t Array5.t;
    var r4444x5:W256.t Array4.t;
    var r1234:W256.t Array5.t;
    var r1234x5:W256.t Array4.t;
    var i:int;
    var rt:W64.t Array3.t;
    var mask26:int;
    var l:W64.t;
    var h:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    var  _10:bool;
    var  _11:bool;
    var  _12:bool;
    var  _13:bool;
    var  _14:bool;
    var  _15:bool;
    var  _16:bool;
    var  _17:bool;
    var  _18:bool;
    var  _19:bool;
    r1234 <- witness;
    r1234x5 <- witness;
    r4444 <- witness;
    r4444x5 <- witness;
    rt <- witness;
    leakages <- LeakFor(0,2) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 2) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- r.[i];
      leakages <- LeakAddr([i]) :: leakages;
      rt.[i] <- aux_0;
      i <- i + 1;
    }
    aux_0 <- (W64.of_int 0);
    leakages <- LeakAddr([2]) :: leakages;
    rt.[2] <- aux_0;
    aux <- 67108863;
    mask26 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(3 + 0)]) :: leakages;
    r1234 <-
    Array5.init
    (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) (3 + 0) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(3 + 4)]) :: leakages;
    r1234 <-
    Array5.init
    (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) (3 + 4) aux_0));
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- rt.[0];
    l <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[1]
    (W8.of_int 52);
     _0 <- aux_5;
     _1 <- aux_4;
     _2 <- aux_3;
     _3 <- aux_2;
     _4 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    h <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(3 + 8)]) :: leakages;
    r1234 <-
    Array5.init
    (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) (3 + 8) aux_0));
    aux_0 <- h;
    l <- aux_0;
    aux_0 <- (l `>>` (W8.of_int 26));
    l <- aux_0;
    aux_0 <- (l `&` (W64.of_int mask26));
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(3 + 12)]) :: leakages;
    r1234 <-
    Array5.init
    (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) (3 + 12) aux_0));
    leakages <- LeakAddr([1]) :: leakages;
    aux_0 <- rt.[1];
    l <- aux_0;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[2]
    (W8.of_int 40);
     _5 <- aux_5;
     _6 <- aux_4;
     _7 <- aux_3;
     _8 <- aux_2;
     _9 <- aux_1;
    l <- aux_0;
    aux_0 <- l;
    leakages <- LeakAddr([(3 + 16)]) :: leakages;
    r1234 <-
    Array5.init
    (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) (3 + 16) aux_0));
    leakages <- LeakFor(0,3) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 3) {
      aux_6 <@ mulmod (rt, r);
      rt <- aux_6;
      aux <- 67108863;
      mask26 <- aux;
      leakages <- LeakAddr([0]) :: leakages;
      aux_0 <- rt.[0];
      l <- aux_0;
      aux_0 <- (l `&` (W64.of_int mask26));
      l <- aux_0;
      aux_0 <- l;
      leakages <- LeakAddr([((2 - i) + 0)]) :: leakages;
      r1234 <-
      Array5.init
      (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) ((2 - i) + 0) aux_0));
      leakages <- LeakAddr([0]) :: leakages;
      aux_0 <- rt.[0];
      l <- aux_0;
      aux_0 <- (l `>>` (W8.of_int 26));
      l <- aux_0;
      aux_0 <- (l `&` (W64.of_int mask26));
      l <- aux_0;
      aux_0 <- l;
      leakages <- LeakAddr([((2 - i) + 4)]) :: leakages;
      r1234 <-
      Array5.init
      (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) ((2 - i) + 4) aux_0));
      leakages <- LeakAddr([0]) :: leakages;
      aux_0 <- rt.[0];
      l <- aux_0;
      leakages <- LeakAddr([1]) :: leakages;
      (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[1]
      (W8.of_int 52);
       _10 <- aux_5;
       _11 <- aux_4;
       _12 <- aux_3;
       _13 <- aux_2;
       _14 <- aux_1;
      l <- aux_0;
      aux_0 <- l;
      h <- aux_0;
      aux_0 <- (l `&` (W64.of_int mask26));
      l <- aux_0;
      aux_0 <- l;
      leakages <- LeakAddr([((2 - i) + 8)]) :: leakages;
      r1234 <-
      Array5.init
      (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) ((2 - i) + 8) aux_0));
      aux_0 <- h;
      l <- aux_0;
      aux_0 <- (l `>>` (W8.of_int 26));
      l <- aux_0;
      aux_0 <- (l `&` (W64.of_int mask26));
      l <- aux_0;
      aux_0 <- l;
      leakages <- LeakAddr([((2 - i) + 12)]) :: leakages;
      r1234 <-
      Array5.init
      (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) ((2 - i) + 12) aux_0));
      leakages <- LeakAddr([1]) :: leakages;
      aux_0 <- rt.[1];
      l <- aux_0;
      leakages <- LeakAddr([2]) :: leakages;
      (aux_5, aux_4, aux_3, aux_2, aux_1, aux_0) <- SHRD_64 l rt.[2]
      (W8.of_int 40);
       _15 <- aux_5;
       _16 <- aux_4;
       _17 <- aux_3;
       _18 <- aux_2;
       _19 <- aux_1;
      l <- aux_0;
      aux_0 <- l;
      leakages <- LeakAddr([((2 - i) + 16)]) :: leakages;
      r1234 <-
      Array5.init
      (WArray160.get256 (WArray160.set64 (WArray160.init256 (fun i => r1234.[i])) ((2 - i) + 16) aux_0));
      i <- i + 1;
    }
    aux_7 <@ times_5 (r1234);
    r1234x5 <- aux_7;
    (aux_8, aux_7) <@ broadcast_r4 (r1234, r1234x5);
    r4444 <- aux_8;
    r4444x5 <- aux_7;
    return (r4444, r4444x5, r1234, r1234x5);
  }

  proc load_avx2 (in_0:W64.t, mask26:W256.t, s_bit25:W256.t) : W256.t Array5.t *
                                                               W64.t = {
    var aux_0: W64.t;
    var aux: W256.t;

    var m:W256.t Array5.t;
    var t:W256.t;
    m <- witness;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 0))))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    t <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 32))))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 32))));
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    aux_0 <- (in_0 + (W64.of_int 64));
    in_0 <- aux_0;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPERM2I128 t m.[1] (W8.of_int (0 %% 2^4 + 2^4 * 2));
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPERM2I128 t m.[1] (W8.of_int (1 %% 2^4 + 2^4 * 3));
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPSRLDQ_256 m.[0] (W8.of_int 6);
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPSRLDQ_256 m.[1] (W8.of_int 6);
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPUNPCKH_4u64 m.[0] m.[1];
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPUNPCKL_4u64 m.[0] m.[1];
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([3] ++ [2]) :: leakages;
    aux <- VPUNPCKL_4u64 m.[2] m.[3];
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] \vshr64u256 (W8.of_int 4));
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (m.[2] `&` mask26);
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (m.[0] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (m.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] \vshr64u256 (W8.of_int 30));
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (m.[4] \vshr64u256 (W8.of_int 40));
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (m.[4] `|` s_bit25);
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (m.[1] `&` mask26);
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    return (m, in_0);
  }

  proc pack_avx2 (h:W256.t Array5.t) : W64.t Array3.t = {
    var aux_2: bool;
    var aux_1: W64.t;
    var aux_0: W128.t;
    var aux: W256.t;

    var r:W64.t Array3.t;
    var t:W256.t Array3.t;
    var u:W256.t Array2.t;
    var t0:W128.t;
    var d:W64.t Array3.t;
    var cf:bool;
    var c:W64.t;
    var cx4:W64.t;
    var  _0:bool;
    var  _1:bool;
    d <- witness;
    r <- witness;
    t <- witness;
    u <- witness;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (h.[1] \vshl64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 h.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (h.[3] \vshl64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u256 h.[2]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPSRLDQ_256 h.[4] (W8.of_int 8);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([4] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u256 h.[4]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPERMQ t.[2]
    (W8.of_int (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * (0 %% 2^2 + 2^2 * 2))));
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPERM2I128 t.[0] t.[1] (W8.of_int (0 %% 2^4 + 2^4 * 2));
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPERM2I128 t.[0] t.[1] (W8.of_int (1 %% 2^4 + 2^4 * 3));
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- (u.[0] \vadd64u256 u.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([2] ++ [0]) :: leakages;
    aux <- VPUNPCKL_4u64 t.[0] t.[2];
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([2] ++ [0]) :: leakages;
    aux <- VPUNPCKH_4u64 t.[0] t.[2];
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- (u.[0] \vadd64u256 u.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- VEXTRACTI128 t.[0] (W8.of_int 1);
    t0 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- VPEXTR_64 (truncateu128 t.[0]) (W8.of_int 0);
    leakages <- LeakAddr([0]) :: leakages;
    d.[0] <- aux_1;
    aux_1 <- VPEXTR_64 t0 (W8.of_int 0);
    leakages <- LeakAddr([1]) :: leakages;
    d.[1] <- aux_1;
    aux_1 <- VPEXTR_64 t0 (W8.of_int 1);
    leakages <- LeakAddr([2]) :: leakages;
    d.[2] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- d.[1];
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    aux_1 <- (r.[0] `<<` (W8.of_int 52));
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- d.[1];
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    aux_1 <- (r.[1] `>>` (W8.of_int 12));
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- d.[2];
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- (r.[2] `>>` (W8.of_int 24));
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- (d.[2] `<<` (W8.of_int 40));
    leakages <- LeakAddr([2]) :: leakages;
    d.[2] <- aux_1;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    (aux_2, aux_1) <- adc_64 r.[0] d.[0] false;
    cf <- aux_2;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_1;
    leakages <- LeakAddr([2] ++ [1]) :: leakages;
    (aux_2, aux_1) <- adc_64 r.[1] d.[2] cf;
    cf <- aux_2;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_2, aux_1) <- adc_64 r.[2] (W64.of_int 0) cf;
     _0 <- aux_2;
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- r.[2];
    c <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- r.[2];
    cx4 <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    aux_1 <- (r.[2] `&` (W64.of_int 3));
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_1;
    aux_1 <- (c `>>` (W8.of_int 2));
    c <- aux_1;
    aux_1 <- (cx4 `&` (W64.of_int (- 4)));
    cx4 <- aux_1;
    aux_1 <- (c + cx4);
    c <- aux_1;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_2, aux_1) <- adc_64 r.[0] c false;
    cf <- aux_2;
    leakages <- LeakAddr([0]) :: leakages;
    r.[0] <- aux_1;
    leakages <- LeakAddr([1]) :: leakages;
    (aux_2, aux_1) <- adc_64 r.[1] (W64.of_int 0) cf;
    cf <- aux_2;
    leakages <- LeakAddr([1]) :: leakages;
    r.[1] <- aux_1;
    leakages <- LeakAddr([2]) :: leakages;
    (aux_2, aux_1) <- adc_64 r.[2] (W64.of_int 0) cf;
     _1 <- aux_2;
    leakages <- LeakAddr([2]) :: leakages;
    r.[2] <- aux_1;
    return (r);
  }

  proc carry_reduce_avx2 (x:W256.t Array5.t, mask26:W256.t) : W256.t Array5.t = {
    var aux: W256.t;

    var z:W256.t Array2.t;
    var t:W256.t;
    z <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (x.[1] \vadd64u256 z.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (x.[4] \vadd64u256 z.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    x.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (x.[1] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (x.[4] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (z.[1] \vshl64u256 (W8.of_int 2));
    t <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (z.[1] \vadd64u256 t);
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (x.[1] `&` mask26);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (x.[4] `&` mask26);
    leakages <- LeakAddr([4]) :: leakages;
    x.[4] <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (x.[2] \vadd64u256 z.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- (x.[0] \vadd64u256 z.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (x.[2] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (x.[2] `&` mask26);
    leakages <- LeakAddr([2]) :: leakages;
    x.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (x.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    x.[0] <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (x.[3] \vadd64u256 z.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (x.[1] \vadd64u256 z.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    x.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (x.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    x.[3] <- aux;
    leakages <- LeakAddr([0] ++ [4]) :: leakages;
    aux <- (x.[4] \vadd64u256 z.[0]);
    leakages <- LeakAddr([4]) :: leakages;
    x.[4] <- aux;
    return (x);
  }

  proc add_mulmod_avx2 (h:W256.t Array5.t, m:W256.t Array5.t,
                        s_r:W256.t Array5.t, s_rx5:W256.t Array4.t,
                        s_mask26:W256.t, s_bit25:W256.t) : W256.t Array5.t = {
    var aux: W256.t;

    var r0:W256.t;
    var r1:W256.t;
    var r4x5:W256.t;
    var t:W256.t Array5.t;
    var u:W256.t Array4.t;
    var r2:W256.t;
    var r3x5:W256.t;
    var r3:W256.t;
    var r2x5:W256.t;
    t <- witness;
    u <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s_r.[0];
    r0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- s_r.[1];
    r1 <- aux;
    leakages <- LeakAddr([(4 - 1)]) :: leakages;
    aux <- s_rx5.[(4 - 1)];
    r4x5 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (h.[0] \vadd64u256 m.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u256 m.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u256 m.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (h.[3] \vadd64u256 m.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([4] ++ [4]) :: leakages;
    aux <- (h.[4] \vadd64u256 m.[4]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r0;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r0;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r0;
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r0;
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r0;
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r1;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r1;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r1;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r1;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- s_r.[2];
    r2 <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u256 u.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([1] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u256 u.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([2] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[2]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([3] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[3]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r4x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r4x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r4x5;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r4x5;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([(3 - 1)]) :: leakages;
    aux <- s_rx5.[(3 - 1)];
    r3x5 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u256 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u256 u.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r2;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r2;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r2;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- s_r.[3];
    r3 <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u256 u.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([1] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[1]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([2] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[2]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r3x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r3x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r3x5;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([(2 - 1)]) :: leakages;
    aux <- s_rx5.[(2 - 1)];
    r2x5 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u256 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u256 t.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r3;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r3;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r2x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r2x5;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u256 t.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([(1 - 1)] ++ [4]) :: leakages;
    aux <- VPMULU_256 h.[4] s_rx5.[(1 - 1)];
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([4] ++ [0]) :: leakages;
    aux <- VPMULU_256 h.[0] s_r.[4];
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- t.[3];
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    return (h);
  }

  proc mainloop_avx2_v1 (h:W256.t Array5.t, m:W256.t Array5.t, in_0:W64.t,
                         s_r:W256.t Array5.t, s_rx5:W256.t Array4.t,
                         s_mask26:W256.t, s_bit25:W256.t) : W256.t Array5.t *
                                                            W256.t Array5.t *
                                                            W64.t = {
    var aux_0: W64.t;
    var aux: W256.t;

    var r0:W256.t;
    var r1:W256.t;
    var r4x5:W256.t;
    var t:W256.t Array5.t;
    var u:W256.t Array4.t;
    var m0:W256.t;
    var r2:W256.t;
    var r3x5:W256.t;
    var r3:W256.t;
    var r2x5:W256.t;
    var mask26:W256.t;
    var z:W256.t Array2.t;
    var z0:W256.t;
    t <- witness;
    u <- witness;
    z <- witness;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- s_r.[0];
    r0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- s_r.[1];
    r1 <- aux;
    leakages <- LeakAddr([(4 - 1)]) :: leakages;
    aux <- s_rx5.[(4 - 1)];
    r4x5 <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (h.[0] \vadd64u256 m.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u256 m.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r0;
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u256 m.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r1;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (h.[3] \vadd64u256 m.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r0;
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([4] ++ [4]) :: leakages;
    aux <- (h.[4] \vadd64u256 m.[4]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r1;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r0;
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r1;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r0;
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u256 u.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r1;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([1] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u256 u.[1]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r0;
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([2] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[2]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([3] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[3]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r4x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 0))))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 0))));
    m0 <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r4x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- s_r.[2];
    r2 <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r4x5;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r4x5;
    leakages <- LeakAddr([3]) :: leakages;
    u.[3] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([LeakageModel.leak_mem ((W64.to_uint (in_0 + (W64.of_int 32))))]) :: leakages;
    aux <- (loadW256 Glob.mem (W64.to_uint (in_0 + (W64.of_int 32))));
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u256 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u256 u.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([3] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[3]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r2;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPERM2I128 m0 m.[1] (W8.of_int (0 %% 2^4 + 2^4 * 2));
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r2;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPERM2I128 m0 m.[1] (W8.of_int (1 %% 2^4 + 2^4 * 3));
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r2;
    leakages <- LeakAddr([2]) :: leakages;
    u.[2] <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (t.[2] \vadd64u256 u.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    t.[2] <- aux;
    leakages <- LeakAddr([(3 - 1)]) :: leakages;
    aux <- s_rx5.[(3 - 1)];
    r3x5 <- aux;
    leakages <- LeakAddr([1] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[1]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([2] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[2]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- VPMULU_256 h.[2] r3x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r3x5;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- s_r.[3];
    r3 <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r3x5;
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPSRLDQ_256 m.[0] (W8.of_int 6);
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPSRLDQ_256 m.[1] (W8.of_int 6);
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (t.[1] \vadd64u256 u.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    t.[1] <- aux;
    leakages <- LeakAddr([2] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u256 t.[2]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([(2 - 1)]) :: leakages;
    aux <- s_rx5.[(2 - 1)];
    r2x5 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- VPMULU_256 h.[0] r3;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- VPMULU_256 h.[1] r3;
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPUNPCKH_4u64 m.[0] m.[1];
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- VPUNPCKL_4u64 m.[0] m.[1];
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (t.[3] \vadd64u256 u.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    t.[3] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    t.[4] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- VPMULU_256 h.[3] r2x5;
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- VPMULU_256 h.[4] r2x5;
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    t.[0] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u256 t.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    aux <- s_mask26;
    mask26 <- aux;
    leakages <- LeakAddr([(1 - 1)] ++ [4]) :: leakages;
    aux <- VPMULU_256 h.[4] s_rx5.[(1 - 1)];
    leakages <- LeakAddr([0]) :: leakages;
    u.[0] <- aux;
    leakages <- LeakAddr([4] ++ [0]) :: leakages;
    aux <- VPMULU_256 h.[0] s_r.[4];
    leakages <- LeakAddr([1]) :: leakages;
    u.[1] <- aux;
    leakages <- LeakAddr([3] ++ [2]) :: leakages;
    aux <- VPUNPCKL_4u64 m.[2] m.[3];
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] \vshr64u256 (W8.of_int 4));
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([0] ++ [0]) :: leakages;
    aux <- (t.[0] \vadd64u256 u.[0]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (h.[0] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (h.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (t.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (t.[3] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (t.[4] \vadd64u256 u.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (m.[2] `&` mask26);
    leakages <- LeakAddr([2]) :: leakages;
    m.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (m.[0] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    leakages <- LeakAddr([0] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u256 z.[0]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([1] ++ [4]) :: leakages;
    aux <- (h.[4] \vadd64u256 z.[1]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (h.[1] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (h.[4] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (z.[1] \vshl64u256 (W8.of_int 2));
    z0 <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (z.[1] \vadd64u256 z0);
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (h.[1] `&` mask26);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (h.[4] `&` mask26);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    leakages <- LeakAddr([0] ++ [2]) :: leakages;
    aux <- (h.[2] \vadd64u256 z.[0]);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([1] ++ [0]) :: leakages;
    aux <- (h.[0] \vadd64u256 z.[1]);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (h.[2] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (h.[0] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([1]) :: leakages;
    z.[1] <- aux;
    leakages <- LeakAddr([2]) :: leakages;
    aux <- (h.[2] `&` mask26);
    leakages <- LeakAddr([2]) :: leakages;
    h.[2] <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (h.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    h.[0] <- aux;
    leakages <- LeakAddr([0] ++ [3]) :: leakages;
    aux <- (h.[3] \vadd64u256 z.[0]);
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([1] ++ [1]) :: leakages;
    aux <- (h.[1] \vadd64u256 z.[1]);
    leakages <- LeakAddr([1]) :: leakages;
    h.[1] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (h.[3] \vshr64u256 (W8.of_int 26));
    leakages <- LeakAddr([0]) :: leakages;
    z.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (h.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    h.[3] <- aux;
    leakages <- LeakAddr([0] ++ [4]) :: leakages;
    aux <- (h.[4] \vadd64u256 z.[0]);
    leakages <- LeakAddr([4]) :: leakages;
    h.[4] <- aux;
    aux_0 <- (in_0 + (W64.of_int 64));
    in_0 <- aux_0;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- (m.[0] `&` mask26);
    leakages <- LeakAddr([0]) :: leakages;
    m.[0] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] \vshr64u256 (W8.of_int 30));
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([3]) :: leakages;
    aux <- (m.[3] `&` mask26);
    leakages <- LeakAddr([3]) :: leakages;
    m.[3] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (m.[4] \vshr64u256 (W8.of_int 40));
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([4]) :: leakages;
    aux <- (m.[4] `|` s_bit25);
    leakages <- LeakAddr([4]) :: leakages;
    m.[4] <- aux;
    leakages <- LeakAddr([1]) :: leakages;
    aux <- (m.[1] `&` mask26);
    leakages <- LeakAddr([1]) :: leakages;
    m.[1] <- aux;
    return (h, m, in_0);
  }

  proc final_avx2_v0 (h:W256.t Array5.t, m:W256.t Array5.t,
                      s_r:W256.t Array5.t, s_rx5:W256.t Array4.t,
                      s_mask26:W256.t, s_bit25:W256.t) : W256.t Array5.t = {
    var aux_0: W256.t;
    var aux: W256.t Array5.t;

    var mask26:W256.t;

    aux <@ add_mulmod_avx2 (h, m, s_r, s_rx5, s_mask26, s_bit25);
    h <- aux;
    aux_0 <- s_mask26;
    mask26 <- aux_0;
    aux <@ carry_reduce_avx2 (h, mask26);
    h <- aux;
    return (h);
  }

  proc poly1305_avx2_update (in_0:W64.t, len:W64.t, r4444:W256.t Array5.t,
                             r4444x5:W256.t Array4.t, r1234:W256.t Array5.t,
                             r1234x5:W256.t Array4.t) : W64.t * W64.t *
                                                        W64.t Array3.t = {
    var aux: int;
    var aux_2: W64.t;
    var aux_0: W256.t;
    var aux_4: W64.t Array3.t;
    var aux_3: W256.t Array5.t;
    var aux_1: W256.t Array5.t;

    var h64:W64.t Array3.t;
    var i:int;
    var h:W256.t Array5.t;
    var t:W256.t;
    var s_mask26:W256.t;
    var mask26:W256.t;
    var s_bit25:W256.t;
    var m:W256.t Array5.t;
    h <- witness;
    h64 <- witness;
    m <- witness;
    leakages <- LeakFor(0,5) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 5) {
      aux_0 <- VPBROADCAST_4u64 zero_u64;
      leakages <- LeakAddr([i]) :: leakages;
      h.[i] <- aux_0;
      i <- i + 1;
    }
    aux_0 <- VPBROADCAST_4u64 mask26_u64;
    t <- aux_0;
    aux_0 <- t;
    s_mask26 <- aux_0;
    aux_0 <- t;
    mask26 <- aux_0;
    aux_0 <- VPBROADCAST_4u64 bit25_u64;
    t <- aux_0;
    aux_0 <- t;
    s_bit25 <- aux_0;
    (aux_3, aux_2) <@ load_avx2 (in_0, mask26, s_bit25);
    m <- aux_3;
    in_0 <- aux_2;

    leakages <- LeakCond(((W64.of_int 128) \ule len)) :: LeakAddr([]) :: leakages;

    while (((W64.of_int 128) \ule len)) {
      (aux_3, aux_1, aux_2) <@ mainloop_avx2_v1 (h, m, in_0, r4444, r4444x5,
      s_mask26, s_bit25);
      h <- aux_3;
      m <- aux_1;
      in_0 <- aux_2;
      aux_2 <- (len - (W64.of_int 64));
      len <- aux_2;
    leakages <- LeakCond(((W64.of_int 128) \ule len)) :: LeakAddr([]) :: leakages;

    }
    aux_2 <- (len - (W64.of_int 64));
    len <- aux_2;
    aux_3 <@ final_avx2_v0 (h, m, r1234, r1234x5, s_mask26, s_bit25);
    h <- aux_3;
    aux_4 <@ pack_avx2 (h);
    h64 <- aux_4;
    return (in_0, len, h64);
  }

  proc poly1305_avx2_wrapper (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {
    var aux_6: W64.t;
    var aux: W64.t;
    var aux_1: W64.t Array3.t;
    var aux_0: W64.t Array3.t;
    var aux_5: W256.t Array4.t;
    var aux_3: W256.t Array4.t;
    var aux_4: W256.t Array5.t;
    var aux_2: W256.t Array5.t;

    var len:W64.t;
    var h:W64.t Array3.t;
    var r:W64.t Array3.t;
    var r4444:W256.t Array5.t;
    var r4444x5:W256.t Array4.t;
    var r1234:W256.t Array5.t;
    var r1234x5:W256.t Array4.t;
    h <- witness;
    r <- witness;
    r1234 <- witness;
    r1234x5 <- witness;
    r4444 <- witness;
    r4444x5 <- witness;
    aux_6 <- inlen;
    len <- aux_6;
    (aux_1, aux_0, aux_6) <@ poly1305_ref3_setup (k);
    h <- aux_1;
    r <- aux_0;
    k <- aux_6;
    (aux_4, aux_5, aux_2, aux_3) <@ poly1305_avx2_setup (r);
    r4444 <- aux_4;
    r4444x5 <- aux_5;
    r1234 <- aux_2;
    r1234x5 <- aux_3;
    (aux_6, aux, aux_1) <@ poly1305_avx2_update (in_0, len, r4444, r4444x5,
    r1234, r1234x5);
    in_0 <- aux_6;
    len <- aux;
    h <- aux_1;
    (aux_6, aux, aux_1) <@ poly1305_ref3_update (in_0, len, h, r);
    in_0 <- aux_6;
    len <- aux;
    h <- aux_1;
    poly1305_ref3_last (out, in_0, len, k, h, r);
    return ();
  }

  proc poly1305_avx2 (out:W64.t, in_0:W64.t, inlen:W64.t, k:W64.t) : unit = {



    leakages <- LeakCond((inlen \ult (W64.of_int 257))) :: LeakAddr([]) :: leakages;
    if ((inlen \ult (W64.of_int 257))) {
      poly1305_ref3_local (out, in_0, inlen, k);
    } else {
      poly1305_avx2_wrapper (out, in_0, inlen, k);
    }
    return ();
  }
}.
end T.
