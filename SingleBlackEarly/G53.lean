import FastCell2
import SegmentCheck
import SingleBlackEarly.C1961
import SingleBlackEarly.C1962
import SingleBlackEarly.C1963
import SingleBlackEarly.C1964
import SingleBlackEarly.C1965
import SingleBlackEarly.C1966
import SingleBlackEarly.C1967
import SingleBlackEarly.C1968
import SingleBlackEarly.C1969
import SingleBlackEarly.C1970
import SingleBlackEarly.C1971
import SingleBlackEarly.C1972
import SingleBlackEarly.C1973
import SingleBlackEarly.C1974
import SingleBlackEarly.C1975
import SingleBlackEarly.C1976
import SingleBlackEarly.C1977
import SingleBlackEarly.C1978
import SingleBlackEarly.C1979
import SingleBlackEarly.C1980
import SingleBlackEarly.C1981
import SingleBlackEarly.C1982
import SingleBlackEarly.C1983
import SingleBlackEarly.C1984
import SingleBlackEarly.C1985
import SingleBlackEarly.C1986
import SingleBlackEarly.C1987
import SingleBlackEarly.C1988
import SingleBlackEarly.C1989
import SingleBlackEarly.C1990
import SingleBlackEarly.C1991
import SingleBlackEarly.C1992
import SingleBlackEarly.C1993
import SingleBlackEarly.C1994
import SingleBlackEarly.C1995
import SingleBlackEarly.C1996
import SingleBlackEarly.C1997

namespace LangtonsAnt

def sbGroup53 : List Point :=
  [(-71, -47), (-69, -48), (-69, -49), (-70, -49), (-68, -49), (-68, -50), (-69, -50), (-68, -48), (-67, -49), (-71, -45), (-72, -45), (-72, -44), (-72, -46), (-73, -46), (-73, -45), (-71, -46), (-72, -47), (-71, -49), (-72, -49), (-72, -48), (-72, -50), (-73, -50), (-73, -49), (-71, -50), (-71, -51), (-72, -51), (-70, -51), (-70, -52), (-71, -52), (-70, -50), (-69, -51), (-73, -47), (-74, -47), (-74, -46), (-74, -48), (-75, -48), (-75, -47)]

theorem sbGroup53_ok : forall q, q ∈ sbGroup53 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup53, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1961
  · exact checkSingleBlackFast2_sound sbCell1962
  · exact checkSingleBlack_sound sbCell1963
  · exact checkSingleBlackFast_sound sbCell1964
  · exact checkSingleBlackFast_sound sbCell1965
  · exact checkSingleBlackFast_sound sbCell1966
  · exact sbCell1967
  · exact checkSingleBlackFast2_sound sbCell1968
  · exact checkSingleBlackFast_sound sbCell1969
  · exact checkSingleBlack_sound sbCell1970
  · exact checkSingleBlackFast_sound sbCell1971
  · exact checkSingleBlackFast2_sound sbCell1972
  · exact checkSingleBlackFast_sound sbCell1973
  · exact checkSingleBlackFast_sound sbCell1974
  · exact checkSingleBlackFast2_sound sbCell1975
  · exact checkSingleBlackFast_sound sbCell1976
  · exact checkSingleBlack_sound sbCell1977
  · exact checkSingleBlackFast2_sound sbCell1978
  · exact checkSingleBlackFast_sound sbCell1979
  · exact checkSingleBlackFast2_sound sbCell1980
  · exact checkSingleBlackFast_sound sbCell1981
  · exact checkSingleBlackFast_sound sbCell1982
  · exact checkSingleBlackFast2_sound sbCell1983
  · exact checkSingleBlackFast2_sound sbCell1984
  · exact checkSingleBlack_sound sbCell1985
  · exact checkSingleBlackFast_sound sbCell1986
  · exact checkSingleBlackFast_sound sbCell1987
  · exact checkSingleBlackFast_sound sbCell1988
  · exact sbCell1989
  · exact checkSingleBlackFast2_sound sbCell1990
  · exact checkSingleBlackFast_sound sbCell1991
  · exact checkSingleBlack_sound sbCell1992
  · exact checkSingleBlackFast_sound sbCell1993
  · exact checkSingleBlackFast2_sound sbCell1994
  · exact checkSingleBlackFast_sound sbCell1995
  · exact checkSingleBlackFast_sound sbCell1996
  · exact checkSingleBlackFast_sound sbCell1997

end LangtonsAnt
