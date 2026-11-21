import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0237 : checkSingleBlackFast (2, 9) 2863 .west (-4, 4) (-15, -6) = true := by
  decide +kernel

end LangtonsAnt
