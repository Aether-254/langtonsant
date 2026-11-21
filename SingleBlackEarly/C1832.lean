import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1832 : checkSingleBlackFast2 (-58, -37) 19509 .east (20, 10) (4, -43) = true := by
  decide +kernel

end LangtonsAnt
