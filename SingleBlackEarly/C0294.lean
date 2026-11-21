import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0294 : checkSingleBlackFast (9, 13) 5375 .west (-9, -9) (-18, -13) = true := by
  decide +kernel

end LangtonsAnt
