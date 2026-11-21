import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0030 : checkSingleBlackFast (2, 3) 1175 .west (-2, 5) (-8, -6) = true := by
  decide +kernel

end LangtonsAnt
