import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2030 : checkSingleBlackFast (-76, -55) 20445 .east (29, 19) (13, -52) = true := by
  decide +kernel

end LangtonsAnt
