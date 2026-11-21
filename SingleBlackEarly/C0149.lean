import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0149 : checkSingleBlackFast (1, 5) 4767 .west (2, 6) (-13, -16) = true := by
  decide +kernel

end LangtonsAnt
