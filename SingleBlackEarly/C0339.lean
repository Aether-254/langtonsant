import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0339 : checkSingleBlackFast (1, 13) 3091 .west (-3, 3) (-16, -7) = true := by
  decide +kernel

end LangtonsAnt
