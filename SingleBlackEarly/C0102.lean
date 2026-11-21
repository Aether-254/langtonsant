import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0102 : checkSingleBlackFast (-4, 6) 9023 .west (-3, 9) (-28, 5) = true := by
  decide +kernel

end LangtonsAnt
