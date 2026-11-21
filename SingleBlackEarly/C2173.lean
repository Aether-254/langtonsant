import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2173 : checkSingleBlackFast (-91, -63) 26361 .east (41, 29) (19, -64) = true := by
  decide +kernel

end LangtonsAnt
