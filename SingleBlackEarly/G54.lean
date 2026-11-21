import FastCell2
import SegmentCheck
import SingleBlackEarly.C1998
import SingleBlackEarly.C1999
import SingleBlackEarly.C2000
import SingleBlackEarly.C2001
import SingleBlackEarly.C2002
import SingleBlackEarly.C2003
import SingleBlackEarly.C2004
import SingleBlackEarly.C2005
import SingleBlackEarly.C2006
import SingleBlackEarly.C2007
import SingleBlackEarly.C2008
import SingleBlackEarly.C2009
import SingleBlackEarly.C2010
import SingleBlackEarly.C2011
import SingleBlackEarly.C2012
import SingleBlackEarly.C2013
import SingleBlackEarly.C2014
import SingleBlackEarly.C2015
import SingleBlackEarly.C2016
import SingleBlackEarly.C2017
import SingleBlackEarly.C2018
import SingleBlackEarly.C2019
import SingleBlackEarly.C2020
import SingleBlackEarly.C2021
import SingleBlackEarly.C2022
import SingleBlackEarly.C2023
import SingleBlackEarly.C2024
import SingleBlackEarly.C2025
import SingleBlackEarly.C2026
import SingleBlackEarly.C2027
import SingleBlackEarly.C2028
import SingleBlackEarly.C2029
import SingleBlackEarly.C2030
import SingleBlackEarly.C2031
import SingleBlackEarly.C2032
import SingleBlackEarly.C2033
import SingleBlackEarly.C2034

namespace LangtonsAnt

def sbGroup54 : List Point :=
  [(-73, -48), (-74, -49), (-73, -51), (-74, -51), (-74, -50), (-74, -52), (-75, -52), (-75, -51), (-73, -52), (-73, -53), (-74, -53), (-72, -53), (-72, -54), (-73, -54), (-72, -52), (-71, -53), (-75, -49), (-76, -49), (-76, -48), (-76, -50), (-77, -50), (-77, -49), (-75, -50), (-76, -51), (-75, -53), (-76, -53), (-76, -52), (-76, -54), (-77, -54), (-77, -53), (-75, -54), (-75, -55), (-76, -55), (-74, -55), (-74, -56), (-75, -56), (-74, -54)]

theorem sbGroup54_ok : forall q, q ∈ sbGroup54 -> EventuallyStandard (singleBlack q) := by
  intro q hq
  simp only [sbGroup54, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSingleBlackFast_sound sbCell1998
  · exact checkSingleBlackFast2_sound sbCell1999
  · exact checkSingleBlackFast2_sound sbCell2000
  · exact checkSingleBlackFast2_sound sbCell2001
  · exact checkSingleBlackFast2_sound sbCell2002
  · exact checkSingleBlackFast2_sound sbCell2003
  · exact checkSingleBlackFast_sound sbCell2004
  · exact checkSingleBlackFast2_sound sbCell2005
  · exact checkSingleBlackFast2_sound sbCell2006
  · exact checkSingleBlack_sound sbCell2007
  · exact checkSingleBlackFast_sound sbCell2008
  · exact checkSingleBlackFast_sound sbCell2009
  · exact checkSingleBlackFast_sound sbCell2010
  · exact sbCell2011
  · exact checkSingleBlackFast2_sound sbCell2012
  · exact checkSingleBlackFast_sound sbCell2013
  · exact checkSingleBlack_sound sbCell2014
  · exact checkSingleBlackFast_sound sbCell2015
  · exact checkSingleBlackFast2_sound sbCell2016
  · exact checkSingleBlackFast_sound sbCell2017
  · exact checkSingleBlackFast_sound sbCell2018
  · exact checkSingleBlackFast_sound sbCell2019
  · exact checkSingleBlackFast_sound sbCell2020
  · exact checkSingleBlackFast2_sound sbCell2021
  · exact checkSingleBlackFast2_sound sbCell2022
  · exact checkSingleBlackFast2_sound sbCell2023
  · exact checkSingleBlackFast2_sound sbCell2024
  · exact checkSingleBlackFast_sound sbCell2025
  · exact checkSingleBlackFast_sound sbCell2026
  · exact checkSingleBlackFast2_sound sbCell2027
  · exact checkSingleBlackFast2_sound sbCell2028
  · exact checkSingleBlack_sound sbCell2029
  · exact checkSingleBlackFast_sound sbCell2030
  · exact checkSingleBlackFast_sound sbCell2031
  · exact checkSingleBlackFast_sound sbCell2032
  · exact checkSingleBlackFast_sound sbCell2033
  · exact checkSingleBlackFast2_sound sbCell2034

end LangtonsAnt
