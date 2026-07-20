From CRIS Require Import CRIS.

Module KVHdr.
  Definition mn := "KV".

  Definition fn (method : string) :=
    mn +:+ "." +:+ method.

  Definition get := fnsig (fn "get") (fntyp Z (option Z)).
  Definition put := fnsig (fn "put") (fntyp (Z * Z) ()).
End KVHdr.

Module KVSource. Section KVSource.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition amap := Z -> option Z.

  Definition empty_map : amap :=
    fun _ => None.

  Definition map_put (m : amap) (k v : Z) : amap :=
    fun q => if Z.eq_dec q k then Some v else m q.

  Definition scopes := [KVHdr.mn].
  Definition v_map := KVHdr.mn ↯ "map".

  Definition get : Z -> itree crisE (option Z) :=
    fun k =>
      'm : amap <- cgetU v_map;;
      Ret (m k).

  Definition put : Z * Z -> itree crisE () :=
    fun kv =>
      let '(k, v) := kv in
      'm : amap <- cgetU v_map;;
      cput v_map (map_put m k v);;;
      Ret tt.

  Definition fnsems : fnsemmap :=
    {[fid KVHdr.get #
        (msk_real (msk_scp scopes msk_true),
          (fsp_none, cfunU KVHdr.get get));
      fid KVHdr.put #
        (msk_real (msk_scp scopes msk_true),
          (fsp_none, cfunU KVHdr.put put))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_map # empty_map↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End KVSource. End KVSource.
