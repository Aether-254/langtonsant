import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1795 : checkSingleBlackFast (-56, -29) 12304 .north (16, 8) (-42, -24) = true := by
  decide +kernel

end LangtonsAnt
