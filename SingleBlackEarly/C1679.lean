import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1679 : checkSingleBlackFast (-42, -23) 19984 .north (23, 19) (-49, -11) = true := by
  decide +kernel

end LangtonsAnt
