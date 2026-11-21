import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1996 : checkSingleBlackFast (-75, -48) 19562 .north (29, 22) (-56, -35) = true := by
  decide +kernel

end LangtonsAnt
