import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0448 : checkSingleBlackFast (19, 8) 4969 .west (-3, 4) (-16, -4) = true := by
  decide +kernel

end LangtonsAnt
