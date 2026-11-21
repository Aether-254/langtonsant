import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2158 : checkSingleBlackFast (-89, -66) 21101 .east (42, 27) (19, -61) = true := by
  decide +kernel

end LangtonsAnt
