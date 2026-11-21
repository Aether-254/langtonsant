import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0668 : checkSingleBlackFast (15, -8) 7707 .west (-4, 6) (-19, -6) = true := by
  decide +kernel

end LangtonsAnt
