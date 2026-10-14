import CSTTT.Transport.RouteLicenseGuards
import Lean

/-! Only evaluated raw definitions, never duplicate export tables. Source
indices are mapped back to JSON identifiers by the read-only check script. -/
namespace CSTTT.RouteLicenses.Models
open Lean
private def obj := Json.mkObj
private def arr (xs : List Json) := Json.arr xs.toArray
private def nat (n : Nat) := toJson n
private def bit (b : Bool) := nat (if b then 1 else 0)
private def fins {n : Nat} (xs : List (Fin n)) := arr (xs.map (fun x => nat x.val))
private def pairs {n : Nat} (xs : List (Fin n × Fin n)) := arr (xs.map (fun p => arr [nat p.1.val,nat p.2.val]))

def exportRaw {nr ne nb nv : Nat} (m : RawSystem (Fin nr) (Fin ne) (Fin nb) (Fin nv) Bool)
    (actions : Fin ne → BitAction) (increments : Fin ne → Bool) (domains : List (Domain (Fin nr) (Fin nb))) : Json :=
  obj [("vertex_count",nat nv),
    ("routes",arr ((List.finRange nr).map fun r => obj [("path",fins (m.path r)),("boundary",nat (m.boundary r).val)])),
    ("events",arr ((List.finRange ne).map fun e => obj [
      ("entry",nat (m.events e).entry.val),("exit",nat (m.events e).exit.val),
      ("available",toJson (m.events e).available),
      ("action_id",nat (match actions e with | .identity => 0 | .toggle => 1)),
      ("action",arr [bit ((m.events e).action false),bit ((m.events e).action true)]),
      ("clock_increment",bit (increments e)),
      ("clock_forward",arr [bit ((m.events e).clockForward false),bit ((m.events e).clockForward true)]),
      ("clock_backward",arr [bit ((m.events e).clockBackward false),bit ((m.events e).clockBackward true)])])),
    ("boundaries",arr ((List.finRange nb).map fun b => obj [
      ("entry",nat (m.boundaries b).entry.val),("exit",nat (m.boundaries b).exit.val),
      ("initial",bit (m.boundaries b).initial)])),
    ("rewrites",pairs m.rewrites),("ranks",arr ((List.finRange nr).map fun r => nat (m.rank r))),
    ("critical",pairs m.critical),
    ("completions",arr (m.completions.map fun c => obj [
      ("left",nat c.left.val),("right",nat c.right.val),("join",nat c.join.val),
      ("left_path",fins c.leftPath),("right_path",fins c.rightPath)])),
    ("domains",arr (domains.map fun d => obj [("boundary",nat d.boundary.val),("routes",fins d.routes)]))]

def routeSnapshot : Json := obj [
  ("actions",arr [arr [bit (BitAction.identity.apply false),bit (BitAction.identity.apply true)],
                     arr [bit (BitAction.toggle.apply false),bit (BitAction.toggle.apply true)]]),
  ("models",arr [exportRaw necessity negAction negClock [necessityDomain],
                  exportRaw positive posAction posClock [positiveDomain 0,positiveDomain 1]])]
end CSTTT.RouteLicenses.Models
